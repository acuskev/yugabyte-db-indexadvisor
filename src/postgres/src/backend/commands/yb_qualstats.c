/*--------------------------------------------------------------------------------------------------
 *
 * yb_qualstats.c
 *		Return index recommendations for a given query based on that query's quals
 * Implementation heavily inspired by pg_qualstats from the Powa-Team
 *
 * Copyright (c) YugaByte, Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License.  You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software distributed under the License
 * is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
 * or implied.  See the License for the specific language governing permissions and limitations
 * under the License.
 *
 * IDENTIFICATION
 *        src/backend/commands/yb_qualstats.c
 *
 *------------------------------------------------------------------------------
 */

#include <limits.h>
#include <math.h>
#include "postgres.h"
#include "access/hash.h"
#include "access/htup_details.h"
#if PG_VERSION_NUM >= 90600
#include "access/parallel.h"
#endif
#if PG_VERSION_NUM >= 100000 && PG_VERSION_NUM < 110000
#include "catalog/pg_authid.h"
#endif
#if PG_VERSION_NUM >= 110000
#include "catalog/pg_authid_d.h"
#endif
#include "catalog/index.h"
#include "catalog/pg_class.h"
#include "catalog/pg_namespace.h"
#include "catalog/pg_operator.h"
#include "catalog/pg_type.h"
#include "commands/dbcommands.h"
#include "commands/explain.h"
#if PG_VERSION_NUM >= 150000
#include "common/pg_prng.h"
#endif
#include "fmgr.h"
#include "funcapi.h"
#include "mb/pg_wchar.h"
#include "miscadmin.h"
#include "nodes/execnodes.h"
#include "nodes/nodeFuncs.h"
#include "nodes/makefuncs.h"
#include "optimizer/clauses.h"
#include "optimizer/planner.h"
#include "parser/analyze.h"
#include "parser/parse_node.h"
#include "parser/parsetree.h"
#if PG_VERSION_NUM >= 150000
#include "postmaster/autovacuum.h"
#endif
#include "postmaster/postmaster.h"
#if PG_VERSION_NUM >= 150000
#include "replication/walsender.h"
#endif
#include "storage/ipc.h"
#include "storage/lwlock.h"
#if PG_VERSION_NUM >= 100000
#include "storage/shmem.h"
#endif
#include "utils/array.h"
#include "utils/builtins.h"
#include "utils/elog.h"
#include "utils/guc.h"
#include "utils/lsyscache.h"
#include "utils/memutils.h"
#include "utils/rel.h"
#include "utils/relcache.h"
#include "utils/tuplestore.h"

PG_MODULE_MAGIC;

#define PGQS_MAX_DEFAULT	1000	/* default pgqs_max value */
#define PGQS_MAX_LOCAL_ENTRIES	(pgqs_max * 0.2)	/* do not track more of
													 * 20% of possible entries
													 * in shared mem */
#define PGQS_CONSTANT_SIZE 80	/* Truncate constant representation at 80 */

#define PGQS_FLAGS (INSTRUMENT_ROWS|INSTRUMENT_BUFFERS)

#define PGQS_NUM	1

/*
 * Extension version number, for supporting older extension versions' objects
 */
typedef enum pgqsVersion
{
	PGQS_V1_0 = 0,
	PGQS_V2_0
} pgqsVersion;

/*---- Function declarations ----*/

static uint32 pgqs_hash_fn(const void *key, Size keysize);
static uint32 pgqs_hash_param_fn(const void *key, Size keysize);
int param_key_compare_fn(const void* lhs, const void* rhs, size_t count);

#if PG_VERSION_NUM < 90500
static uint32 pgqs_uint32_hashfn(const void *key, Size keysize);
#endif

static int	pgqs_max = PGQS_MAX_DEFAULT;			/* max # statements to track */
static bool pgqs_track_pgcatalog;	/* track queries on pg_catalog */
static bool pgqs_resolve_oids;	/* resolve oids */
static bool pgqs_track_constants = true;


/*---- Data structures declarations ----*/

/* Since cff440d368, queryid becomes a uint64 internally. */

#if PG_VERSION_NUM >= 110000
typedef uint64 pgqs_queryid;
#else
typedef uint32 pgqs_queryid;
#endif

typedef struct pgqsHashKey
{
	Oid			userid;			/* user OID */
	Oid			dbid;			/* database OID */
	pgqs_queryid queryid;		/* query identifier (if set by another plugin */
	uint32		uniquequalnodeid;	/* Hash of the const */
	uint32		uniquequalid;	/* Hash of the parent, including the consts */
	char		evaltype;		/* Evaluation type. Can be 'f' to mean a qual
								 * executed after a scan, or 'i' for an
								 * indexqual */
} pgqsHashKey;

typedef struct pgqsParamKey
{
	int paramno;
} pgqsParamKey;

typedef struct pgqsParamEntry
{
	pgqsParamKey 	key;
	Var*			var;
} pgqsParamEntry;

typedef struct pgqsNames
{
	NameData	rolname;
	NameData	datname;
	NameData	lrelname;
	NameData	lattname;
	NameData	opname;
	NameData	rrelname;
	NameData	rattname;
} pgqsNames;

typedef struct pgqsEntry
{
	pgqsHashKey key;
	Oid			lrelid;			/* LHS relation OID or NULL if not var */
	AttrNumber	lattnum;		/* LHS attribute Number or NULL if not var */
	Oid			opoid;			/* Operator OID */
	Oid			rrelid;			/* RHS relation OID or NULL if not var */
	AttrNumber	rattnum;		/* RHS attribute Number or NULL if not var */
	char		constvalue[PGQS_CONSTANT_SIZE]; /* Textual representation of
												 * the right hand constant, if
												 * any */
	uint32		qualid;			/* Hash of the parent AND expression if any, 0
								 * otherwise. */
	uint32		qualnodeid;		/* Hash of the node itself */

	int			position;		/* content position in query text */
	double		usage;			/* # of qual execution, used for deallocation */
	int64		occurences;		/* # of qual execution, 1 per query */
} pgqsEntry;

typedef struct pgqsEntryWithNames
{
	pgqsEntry	entry;
	pgqsNames	names;
} pgqsEntryWithNames;

typedef struct pgqsQueryStringHashKey
{
	pgqs_queryid queryid;
} pgqsQueryStringHashKey;

/*
 * Transient state of the query tree walker - for the meaning of the counters,
 * see pgqsEntry comments.
 */
typedef struct pgqsWalkerContext
{
	pgqs_queryid queryId;
	List	   *rtable;
	PlanState  *planstate;
	PlanState  *inner_planstate;
	PlanState  *outer_planstate;
	List	   *outer_tlist;
	List	   *inner_tlist;
	List	   *index_tlist;
	uint32		qualid;
	uint32		uniquequalid;	/* Hash of the parent, including the consts */
	double		err_estim[2];
	int			nentries;		/* number of entries found so far */
	char		evaltype;
	const char *querytext;
} pgqsWalkerContext;


static bool pgqs_whereclause_tree_walker(Node *node, pgqsWalkerContext *query);
static pgqsEntry *pgqs_process_opexpr(OpExpr *expr, pgqsWalkerContext *context);
static pgqsEntry *pgqs_process_scalararrayopexpr(ScalarArrayOpExpr *expr,
											pgqsWalkerContext *context);
static pgqsEntry *pgqs_process_booltest(BooleanTest *expr, pgqsWalkerContext *context);
static void pgqs_collectNodeStats(PlanState *planstate, List *ancestors,
							pgqsWalkerContext *context);
static void pgqs_collectMemberNodeStats(int nplans, PlanState **planstates, List *ancestors,
									pgqsWalkerContext *context);
static void pgqs_collectSubPlanStats(List *plans, List *ancestors, pgqsWalkerContext *context);
static uint32 hashExpr(Expr *expr, pgqsWalkerContext *context, bool include_const);
static void exprRepr(Expr *expr, StringInfo buffer, pgqsWalkerContext *context, bool include_const);
static void pgqs_set_planstates(PlanState *planstate, pgqsWalkerContext *context);
static Expr *pgqs_resolve_var(Var *var, pgqsWalkerContext *context);
static void add_params_to_hash(List *nestParams);
static void determine_index_exists(ExplainState *es, pgqsEntry *entry, Oid relid,
								AttrNumber attnum, int strategy);

static inline void pgqs_entry_init(pgqsEntry *entry);
static inline void pgqs_entry_copy_raw(pgqsEntry *dest, pgqsEntry *src);
static void pgqs_fillnames(pgqsEntryWithNames *entry);

/* Local Hash */
static HTAB *pgqs_localhash = NULL;
static HTAB *pgqs_paramhash= NULL;


/*
 * Do catalog search to replace oids with corresponding objects name
 */
void
pgqs_fillnames(pgqsEntryWithNames *entry)
{
#if PG_VERSION_NUM >= 110000
#define GET_ATTNAME(r, a)	get_attname(r, a, false)
#else
#define GET_ATTNAME(r, a)	get_attname(r, a)
#endif

#if PG_VERSION_NUM >= 90500
	namestrcpy(&(entry->names.rolname), GetUserNameFromId(entry->entry.key.userid, true));
#else
	namestrcpy(&(entry->names.rolname), GetUserNameFromId(entry->entry.key.userid));
#endif
	namestrcpy(&(entry->names.datname), get_database_name(entry->entry.key.dbid));

	if (entry->entry.lrelid != InvalidOid)
	{
		namestrcpy(&(entry->names.lrelname),
				   get_rel_name(entry->entry.lrelid));
		namestrcpy(&(entry->names.lattname),
				   GET_ATTNAME(entry->entry.lrelid, entry->entry.lattnum));
	}

	if (entry->entry.opoid != InvalidOid)
		namestrcpy(&(entry->names.opname), get_opname(entry->entry.opoid));

	if (entry->entry.rrelid != InvalidOid)
	{
		namestrcpy(&(entry->names.rrelname),
				   get_rel_name(entry->entry.rrelid));
		namestrcpy(&(entry->names.rattname),
				   GET_ATTNAME(entry->entry.rrelid, entry->entry.rattnum));
	}
#undef GET_ATTNAME
}

/*
 * Save a non normalized query for the queryid if no one already exists, and
 * do all the stat collecting job
 */
extern void
yb_advisor(ExplainState* es, QueryDesc *queryDesc)
{
	pgqsQueryStringHashKey queryKey;

	HASHCTL		info;
	HASHCTL		info_param;
	pgqsEntry  *localentry;
	HASH_SEQ_STATUS local_hash_seq;
	pgqsWalkerContext *context = palloc(sizeof(pgqsWalkerContext));

	context->queryId = queryDesc->plannedstmt->queryId;
	context->rtable = queryDesc->plannedstmt->rtable;
	context->qualid = 0;
	context->uniquequalid = 0;
	context->evaltype = 0;
	context->nentries = 0;
	context->querytext = queryDesc->sourceText;
	queryKey.queryid = context->queryId;

	/* create local hash table if it hasn't been created yet */
	if (!pgqs_localhash)
	{
		memset(&info, 0, sizeof(info));
		info.keysize = sizeof(pgqsHashKey);

		if (pgqs_resolve_oids)
			info.entrysize = sizeof(pgqsEntryWithNames);
		else
			info.entrysize = sizeof(pgqsEntry);

		info.hash = pgqs_hash_fn;

		pgqs_localhash = hash_create("pgqs_localhash",
										50,
										&info,
										HASH_ELEM | HASH_FUNCTION);
	}

	/* create local param table if it hasn't been created yet */
	if (!pgqs_paramhash)
	{
		memset(&info_param, 0, sizeof(info_param));
		info_param.keysize = sizeof(pgqsParamKey);

		info_param.entrysize = sizeof(pgqsParamEntry);

		info_param.hash = pgqs_hash_param_fn;

		info_param.match = (HashCompareFunc) param_key_compare_fn;

		pgqs_paramhash = hash_create("pgqs_paramhash",
										50,
										&info_param,
										HASH_ELEM | HASH_FUNCTION | HASH_COMPARE);
	}

	/* retrieve quals */
	pgqs_collectNodeStats(queryDesc->planstate, NIL, context);

	hash_seq_init(&local_hash_seq, pgqs_localhash);
	while ((localentry = hash_seq_search(&local_hash_seq)) != NULL)
	{
		// elog(LOG, "from hashtable: entry qualid: %d, constvalue: %s, lattnum: %d, opoid: %d, lrelid: %d, rrelid: %d", localentry->qualid, localentry->constvalue, localentry->lattnum, localentry->opoid, localentry->lrelid, localentry->rrelid);

		List* families = get_op_btree_interpretation(localentry->opoid);
		// presently families will contain both btree and lsm families for the op, strategy numbers
		// are the same so we default to first family
		OpBtreeInterpretation *fam = (OpBtreeInterpretation *) lfirst(families->head);

		if (localentry->lrelid != 0)
		{
			determine_index_exists(es, localentry, localentry->lrelid,
				localentry->lattnum, fam->strategy);
		}
		if (localentry->rrelid != 0)
		{
			determine_index_exists(es, localentry, localentry->rrelid,
				localentry->rattnum, fam->strategy);
		}

		/* cleanup local hash */
		hash_search(pgqs_localhash, &localentry->key, HASH_REMOVE, NULL);
	}
}

static void determine_index_exists(ExplainState* es, pgqsEntry *entry, Oid relid,
								AttrNumber attnum, int strategy) {

	Relation rel = heap_open( relid, AccessShareLock );
	bool existing_index = false;
	ListCell	*index_cell;
	List		*index_oids = RelationGetIndexList( rel );
	char* attname = get_attname(relid, attnum, false);
	char* relname = get_rel_name(relid);

	foreach( index_cell, index_oids )
	{
		/* open index relation and get the index info */
		Oid			index_oid	= lfirst_oid( index_cell );
		Relation	index_rel	= index_open( index_oid,
													AccessShareLock );
		IndexInfo	*index_info	= BuildIndexInfo( index_rel );

		/* We ignore expressional indexes and partial indexes */
		if( index_rel->rd_index->indisvalid
			&& index_info->ii_Expressions == NIL
			&& index_info->ii_Predicate == NIL )
		{
			Assert( index_info->ii_Expressions == NIL );
			Assert( index_info->ii_Predicate == NIL );

			/* search for a matching candidate among the single column indexes of this table */
			if (index_info->ii_NumIndexAttrs == 1)
			{
				if (attnum == index_info->ii_IndexAttrNumbers[0])
				{
					// we assume only single key column, and hardcode rd_indoption accordingly
					// because we only look at single column indexes for now.
					if (strategy == 3 && index_rel->rd_indoption[1] & INDOPTION_HASH)
					{
						existing_index = true;
						// appendStringInfo(es->str, "EXISTING INDEX: strategy number is 3, hash index on relation %s, column %s \n", relname, attname);
						elog(LOG, "EXISTING INDEX: strategy number is 3, recommend hash index on relation %s, column %s", relname, attname);
					}
					else if (strategy != 3 && !(index_rel->rd_indoption[1] & INDOPTION_HASH))
					{
						existing_index = true;
						// appendStringInfo(es->str, "EXISTING INDEX: strategy number is %d, range index on relation %s, column %s \n", strategy, relname, attname);
						elog(LOG, "EXISTING INDEX: strategy number is %d, recommend range index on relation %s, column %s", strategy, relname, attname);
					}
				}
			}
		}
		/* close index relation and free index info */
		index_close( index_rel, AccessShareLock );
		pfree( index_info );
	}

	if (!existing_index)
	{
		if (strategy == 3) {
			appendStringInfo(es->str, "NEW INDEX: Recommend hash index on relation %s, column %s \n", relname, attname);
			elog(LOG, "NEW INDEX: strategy number is 3, recommend hash index on relation %s, column %s", relname, attname);
		}
		else {
			appendStringInfo(es->str, "NEW INDEX: Recommend range index on relation %s, column %s \n", relname, attname);
			elog(LOG, "NEW INDEX: strategy number is %d, recommend range index on relation %s, column %s", strategy, relname, attname);
		}
	}

	/* free the list of existing index Oids */
	list_free( index_oids );
	heap_close( rel, AccessShareLock );
}

/* Initialize all non-key fields of the given entry. */
static inline void
pgqs_entry_init(pgqsEntry *entry)
{
	/* Note that pgqsNames if needed will be explicitly filled after this */
	memset(&(entry->lrelid), 0, sizeof(pgqsEntry) - sizeof(pgqsHashKey));
}

/* Copy non-key and non-name fields from the given entry */
static inline void
pgqs_entry_copy_raw(pgqsEntry *dest, pgqsEntry *src)
{
	/* Note that pgqsNames if needed will be explicitly filled after this */
	memcpy(&(dest->lrelid),
		   &(src->lrelid),
		   (sizeof(pgqsEntry) - sizeof(pgqsHashKey)));
}

static void
pgqs_collectNodeStats(PlanState *planstate, List *ancestors, pgqsWalkerContext *context)
{
	Plan	   *plan = planstate->plan;
	double		old_err_num = context->err_estim[PGQS_NUM];
	ListCell   *lc;
	List	   *parent = 0;
	List	   *indexquals = 0;
	List	   *quals = 0;

	context->planstate = planstate;

	/* Retrieve the generic quals and indexquals */
	switch (nodeTag(plan))
	{
		case T_IndexOnlyScan:
			indexquals = ((IndexOnlyScan *) plan)->indexqual;
			quals = plan->qual;
			break;
		case T_IndexScan:
			indexquals = ((IndexScan *) plan)->indexqualorig;
			quals = plan->qual;
			break;
		case T_BitmapIndexScan:
			indexquals = ((BitmapIndexScan *) plan)->indexqualorig;
			quals = plan->qual;
			break;
		case T_CteScan:
		case T_SeqScan:
		case T_BitmapHeapScan:
		case T_TidScan:
		case T_SubqueryScan:
		case T_FunctionScan:
		case T_ValuesScan:
		case T_WorkTableScan:
		case T_ForeignScan:
		case T_ModifyTable:
			quals = plan->qual;
			break;
		case T_NestLoop:
			quals = ((NestLoop *) plan)->join.joinqual;
			add_params_to_hash(((NestLoop *) plan)->nestParams);
			break;
		case T_MergeJoin:
			quals = ((MergeJoin *) plan)->mergeclauses;
			break;
		case T_HashJoin:
			quals = ((HashJoin *) plan)->hashclauses;
			break;
		default:
			break;

	}

	pgqs_set_planstates(planstate, context);
	parent = list_union(indexquals, quals);
	if (list_length(parent) > 1)
	{
		context->uniquequalid = hashExpr((Expr *) parent, context, true);
		context->qualid = hashExpr((Expr *) parent, context, false);
	}

	/* Add the indexquals */
	context->evaltype = 'i';
	expression_tree_walker((Node *) indexquals,
							pgqs_whereclause_tree_walker, context);

	/* Add the generic quals */
	context->evaltype = 'f';
	expression_tree_walker((Node *) quals, pgqs_whereclause_tree_walker,
							context);

	context->qualid = 0;
	context->uniquequalid = 0;
	context->err_estim[PGQS_NUM] = old_err_num;

	foreach(lc, planstate->initPlan)
	{
		SubPlanState *sps = (SubPlanState *) lfirst(lc);

		pgqs_collectNodeStats(sps->planstate, ancestors, context);
	}

	/* lefttree */
	if (outerPlanState(planstate))
		pgqs_collectNodeStats(outerPlanState(planstate), ancestors, context);

	/* righttree */
	if (innerPlanState(planstate))
		pgqs_collectNodeStats(innerPlanState(planstate), ancestors, context);

	/* special child plans */
	switch (nodeTag(plan))
	{
#if PG_VERSION_NUM < 140000
		case T_ModifyTable:
			pgqs_collectMemberNodeStats(((ModifyTableState *) planstate)->mt_nplans,
										((ModifyTableState *) planstate)->mt_plans,
										ancestors, context);
			break;
#endif
		case T_Append:
			pgqs_collectMemberNodeStats(((AppendState *) planstate)->as_nplans,
										((AppendState *) planstate)->appendplans,
										ancestors, context);
			break;
		case T_MergeAppend:
			pgqs_collectMemberNodeStats(((MergeAppendState *) planstate)->ms_nplans,
										((MergeAppendState *) planstate)->mergeplans,
										ancestors, context);
			break;
		case T_BitmapAnd:
			pgqs_collectMemberNodeStats(((BitmapAndState *) planstate)->nplans,
										((BitmapAndState *) planstate)->bitmapplans,
										ancestors, context);
			break;
		case T_BitmapOr:
			pgqs_collectMemberNodeStats(((BitmapOrState *) planstate)->nplans,
										((BitmapOrState *) planstate)->bitmapplans,
										ancestors, context);
			break;
		case T_SubqueryScan:
			pgqs_collectNodeStats(((SubqueryScanState *) planstate)->subplan, ancestors, context);
			break;
		default:
			break;
	}

	/* subPlan-s */
	if (planstate->subPlan)
		pgqs_collectSubPlanStats(planstate->subPlan, ancestors, context);
}

static void
pgqs_collectMemberNodeStats(int nplans, PlanState **planstates,
							List *ancestors, pgqsWalkerContext *context)
{
	int			i;

	for (i = 0; i < nplans; i++)
		pgqs_collectNodeStats(planstates[i], ancestors, context);
}

static void
pgqs_collectSubPlanStats(List *plans, List *ancestors, pgqsWalkerContext *context)
{
	ListCell   *lst;

	foreach(lst, plans)
	{
		SubPlanState *sps = (SubPlanState *) lfirst(lst);

		pgqs_collectNodeStats(sps->planstate, ancestors, context);
	}
}

static pgqsEntry *
pgqs_process_scalararrayopexpr(ScalarArrayOpExpr *expr, pgqsWalkerContext *context)
{
	OpExpr	   *op = makeNode(OpExpr);
	int			len = 0;
	pgqsEntry  *entry = NULL;
	Expr	   *array = lsecond(expr->args);

	op->opno = expr->opno;
	op->opfuncid = expr->opfuncid;
	op->inputcollid = expr->inputcollid;
	op->opresulttype = BOOLOID;
	op->args = expr->args;
	switch (array->type)
	{
		case T_ArrayExpr:
			len = list_length(((ArrayExpr *) array)->elements);
			break;
		case T_Const:
			/* Const is an array. */
			{
				Const	   *arrayconst = (Const *) array;
				ArrayType  *array_type;

				if (arrayconst->constisnull)
					return NULL;

				array_type = DatumGetArrayTypeP(arrayconst->constvalue);

				if (ARR_NDIM(array_type) > 0)
					len = ARR_DIMS(array_type)[0];
			}
			break;
		default:
			break;
	}

	if (len > 0)
	{
		entry = pgqs_process_opexpr(op, context);
	}

	return entry;
}

static pgqsEntry *
pgqs_process_booltest(BooleanTest *expr, pgqsWalkerContext *context)
{
	pgqsHashKey key;
	pgqsEntry  *entry;
	bool		found;
	Var		   *var;
	Expr	   *newexpr = NULL;
	char	   *constant;
	Oid			opoid;
	RangeTblEntry *rte;

	/* do not store more than 20% of possible entries in shared mem */
	if (context->nentries >= PGQS_MAX_LOCAL_ENTRIES)
		return NULL;

	if (IsA(expr->arg, Var))
		newexpr = pgqs_resolve_var((Var *) expr->arg, context);

	if (!(newexpr && IsA(newexpr, Var)))
		return NULL;

	var = (Var *) newexpr;
	rte = list_nth(context->rtable, var->varno - 1);
	switch (expr->booltesttype)
	{
		case IS_TRUE:
			constant = "TRUE::bool";
			opoid = BooleanEqualOperator;
			break;
		case IS_FALSE:
			constant = "FALSE::bool";
			opoid = BooleanEqualOperator;
			break;
		case IS_NOT_TRUE:
			constant = "TRUE::bool";
			opoid = BooleanNotEqualOperator;
			break;
		case IS_NOT_FALSE:
			constant = "FALSE::bool";
			opoid = BooleanNotEqualOperator;
			break;
		case IS_UNKNOWN:
			constant = "NULL::bool";
			opoid = BooleanEqualOperator;
			break;
		case IS_NOT_UNKNOWN:
			constant = "NULL::bool";
			opoid = BooleanNotEqualOperator;
			break;
		default:
			/* Bail out */
			return NULL;
	}
	memset(&key, 0, sizeof(pgqsHashKey));
	key.userid = GetUserId();
	key.dbid = MyDatabaseId;
	key.uniquequalid = context->uniquequalid;
	key.uniquequalnodeid = hashExpr((Expr *) expr, context, pgqs_track_constants);
	key.queryid = context->queryId;
	key.evaltype = context->evaltype;

	/* local hash, no lock needed */
	entry = (pgqsEntry *) hash_search(pgqs_localhash, &key, HASH_ENTER, &found);
	if (!found)
	{
		context->nentries++;

		pgqs_entry_init(entry);
		entry->qualnodeid = hashExpr((Expr *) expr, context, false);
		entry->qualid = context->qualid;
		entry->opoid = opoid;

		if (rte->rtekind == RTE_RELATION)
		{
			entry->lrelid = rte->relid;
			entry->lattnum = var->varattno;
		}

		if (pgqs_track_constants)
		{
			char	   *utf8const = (char *) pg_do_encoding_conversion((unsigned char *) constant,
																	   strlen(constant),
																	   GetDatabaseEncoding(),
																	   PG_UTF8);

			Assert(strlen(utf8const) < PGQS_CONSTANT_SIZE);
			strcpy(entry->constvalue, utf8const);
		}
		else
			memset(entry->constvalue, 0, sizeof(char) * PGQS_CONSTANT_SIZE);

		if (pgqs_resolve_oids)
			pgqs_fillnames((pgqsEntryWithNames *) entry);
	}

	entry->usage += 1;

	return entry;
}

static void
get_const_expr(Const *constval, StringInfo buf)
{
	Oid			typoutput;
	bool		typIsVarlena;
	char	   *extval;

	if (constval->constisnull)
	{
		/*
		 * Always label the type of a NULL constant to prevent misdecisions
		 * about type when reparsing.
		 */
		appendStringInfoString(buf, "NULL");
		appendStringInfo(buf, "::%s",
						 format_type_with_typemod(constval->consttype,
												  constval->consttypmod));
		return;
	}

	getTypeOutputInfo(constval->consttype, &typoutput, &typIsVarlena);
	extval = OidOutputFunctionCall(typoutput, constval->constvalue);

	switch (constval->consttype)
	{
		case INT2OID:
		case INT4OID:
		case INT8OID:
		case OIDOID:
		case FLOAT4OID:
		case FLOAT8OID:
		case NUMERICOID:
			{
				/*
				 * These types are printed without quotes unless they contain
				 * values that aren't accepted by the scanner unquoted (e.g.,
				 * 'NaN').  Note that strtod() and friends might accept NaN,
				 * so we can't use that to test.
				 *
				 * In reality we only need to defend against infinity and NaN,
				 * so we need not get too crazy about pattern matching here.
				 *
				 * There is a special-case gotcha: if the constant is signed,
				 * we need to parenthesize it, else the parser might see a
				 * leading plus/minus as binding less tightly than adjacent
				 * operators --- particularly, the cast that we might attach
				 * below.
				 */
				if (strspn(extval, "0123456789+-eE.") == strlen(extval))
				{
					if (extval[0] == '+' || extval[0] == '-')
						appendStringInfo(buf, "(%s)", extval);
					else
						appendStringInfoString(buf, extval);
				}
				else
					appendStringInfo(buf, "'%s'", extval);
			}
			break;

		case BITOID:
		case VARBITOID:
			appendStringInfo(buf, "B'%s'", extval);
			break;

		case BOOLOID:
			if (strcmp(extval, "t") == 0)
				appendStringInfoString(buf, "true");
			else
				appendStringInfoString(buf, "false");
			break;

		default:
			appendStringInfoString(buf, quote_literal_cstr(extval));
			break;
	}

	pfree(extval);

	/*
	 * For showtype == 0, append ::typename unless the constant will be
	 * implicitly typed as the right type when it is read in.
	 */
	appendStringInfo(buf, "::%s",
					 format_type_with_typemod(constval->consttype,
											  constval->consttypmod));

}

/*-----------
 * In order to avoid duplicated entries for sementically equivalent OpExpr,
 * this function returns a canonical version of the given OpExpr.
 *
 * For now, the only modification is for OpExpr with a Var and a Const, we
 * prefer the form:
 * Var operator Const
 * with the Var on the LHS.  If the expression in the opposite form and the
 * operator has a commutator, we'll commute it, otherwise fallback to the
 * original OpExpr with the Var on the RHS.
 * OpExpr of the form Var operator Var can still be redundant.
 */
static OpExpr *
pgqs_get_canonical_opexpr(OpExpr *expr, bool *commuted)
{
	if (commuted)
		*commuted = false;

	/* Only OpExpr with 2 arguments needs special processing. */
	if (list_length(expr->args) != 2)
		return expr;

	/* If the 1st argument is a Var, nothing is done */
	if (IsA(linitial(expr->args), Var))
		return expr;

	/* If the 2nd argument is a Var, commute the OpExpr if possible */
	if (IsA(lsecond(expr->args), Var) && OidIsValid(get_commutator(expr->opno)))
	{
		OpExpr	   *newexpr = copyObject(expr);

		CommuteOpExpr(newexpr);

		if (commuted)
			*commuted = true;

		return newexpr;
	}

	return expr;
}

static pgqsEntry *
pgqs_process_opexpr(OpExpr *expr, pgqsWalkerContext *context)
{
	/* do not store more than 20% of possible entries in shared mem */
	if (context->nentries >= PGQS_MAX_LOCAL_ENTRIES)
		return NULL;

	if (list_length(expr->args) == 2)
	{
		bool		save_qual;
		Node	   *node;
		Var		   *var;
		Const	   *constant;
		Oid		   *sreliddest;
		AttrNumber *sattnumdest;
		pgqsEntry	tempentry;
		int			step;

		pgqs_entry_init(&tempentry);
		tempentry.opoid = expr->opno;

		save_qual = false;
		var = NULL;				/* will store the last Var found, if any */
		constant = NULL;		/* will store the last Constant found, if any */

		/* setup the node and LHS destination fields for the 1st argument */
		node = linitial(expr->args);
		sreliddest = &(tempentry.lrelid);
		sattnumdest = &(tempentry.lattnum);

		for (step = 0; step < 2; step++)
		{
			if (IsA(node, RelabelType))
				node = (Node *) ((RelabelType *) node)->arg;

			if (IsA(node, Var))
				node = (Node *) pgqs_resolve_var((Var *) node, context);

			if (IsA(node, Param))
			{
				pgqsParamKey key;
				bool found;
				key.paramno = ((Param *) node)->paramid;

				pgqsParamEntry* paramentry;
				paramentry = (pgqsParamEntry *) hash_search(pgqs_paramhash, &key, HASH_FIND,
								&found);

				node = (Node *) paramentry->var;

				// clean up after
				hash_search(pgqs_paramhash, &key, HASH_REMOVE,
								NULL);
			}

			switch (node->type)
			{
				case T_Var:
					var = (Var *) node;
					{
						RangeTblEntry *rte;

						rte = list_nth(context->rtable, var->varnoold - 1);
						if (rte->rtekind == RTE_RELATION)
						{
							save_qual = true;
							*sreliddest = rte->relid;
							*sattnumdest = var->varattno;
						}
						else
							var = NULL;
					}
					break;
				case T_Const:
					constant = (Const *) node;
					break;
				default:
					break;
			}

			/* find the node to process for the 2nd pass */
			if (step == 0)
			{
				node = NULL;

				if (var == NULL)
				{
					bool		commuted;
					OpExpr	   *newexpr = pgqs_get_canonical_opexpr(expr, &commuted);

					/*
					 * If the OpExpr was commuted we have to use the 1st
					 * argument of the new OpExpr, and keep using the LHS as
					 * destination fields.
					 */
					if (commuted)
					{
						Assert(sreliddest == &(tempentry.lrelid));
						Assert(sattnumdest == &(tempentry.lattnum));

						node = linitial(newexpr->args);
					}
				}

				/*
				 * If the 1st argument was a var, or if it wasn't and the
				 * operator couldn't be commuted, use the 2nd argument and the
				 * RHS as destination fields.
				 */
				if (node == NULL)
				{
					/* simply process the next argument */
					node = lsecond(expr->args);

					/*
					 * a Var was found and stored on the LHS, so if the next
					 * node  will be stored on the RHS
					 */
					sreliddest = &(tempentry.rrelid);
					sattnumdest = &(tempentry.rattnum);
				}
			}
		}

		if (save_qual)
		{
			pgqsHashKey key;
			pgqsEntry  *entry;
			StringInfo	buf = makeStringInfo();
			bool		found;
			int			position = -1;

			/*
			 * If we don't track rels in the pg_catalog schema, lookup the
			 * schema to make sure its not pg_catalog. Otherwise, bail out.
			 */
			if (!pgqs_track_pgcatalog)
			{
				Oid			nsp;

				if (tempentry.lrelid != InvalidOid)
				{
					nsp = get_rel_namespace(tempentry.lrelid);

					Assert(OidIsValid(nsp));

					if (nsp == PG_CATALOG_NAMESPACE)
						return NULL;
				}

				if (tempentry.rrelid != InvalidOid)
				{
					nsp = get_rel_namespace(tempentry.rrelid);

					Assert(OidIsValid(nsp));

					if (nsp == PG_CATALOG_NAMESPACE)
						return NULL;
				}
			}

			if (constant != NULL && pgqs_track_constants)
			{
				get_const_expr(constant, buf);
				position = constant->location;
			}

			memset(&key, 0, sizeof(pgqsHashKey));
			key.userid = GetUserId();
			key.dbid = MyDatabaseId;
			key.uniquequalid = context->uniquequalid;
			key.uniquequalnodeid = hashExpr((Expr *) expr, context, pgqs_track_constants);
			key.queryid = context->queryId;
			key.evaltype = context->evaltype;

			/* local hash, no lock needed */
			entry = (pgqsEntry *) hash_search(pgqs_localhash, &key, HASH_ENTER,
											  &found);
			if (!found)
			{
				char	   *utf8const;
				int			len;

				context->nentries++;

				/* raw copy the temporary entry */
				pgqs_entry_copy_raw(entry, &tempentry);
				entry->position = position;
				entry->qualnodeid = hashExpr((Expr *) expr, context, false);
				entry->qualid = context->qualid;

				utf8const = (char *) pg_do_encoding_conversion((unsigned char *) buf->data,
															   strlen(buf->data),
															   GetDatabaseEncoding(),
															   PG_UTF8);
				len = strlen(utf8const);

				/*
				 * The const value can use multibyte characters, so we need to
				 * be careful when truncating the value.  Note that we need to
				 * use PG_UTF8 encoding explicitly here, as the value was just
				 * converted to this encoding.
				 */
				len = pg_encoding_mbcliplen(PG_UTF8, utf8const, len,
											PGQS_CONSTANT_SIZE - 1);

				memcpy(entry->constvalue, utf8const, len);
				entry->constvalue[len] = '\0';

				if (pgqs_resolve_oids)
					pgqs_fillnames((pgqsEntryWithNames *) entry);
			}

			entry->usage += 1;

			return entry;
		}
	}

	return NULL;
}

static bool
pgqs_whereclause_tree_walker(Node *node, pgqsWalkerContext *context)
{
	if (node == NULL)
		return false;

	switch (node->type)
	{
		case T_BoolExpr:
			{
				BoolExpr   *boolexpr = (BoolExpr *) node;

				if (boolexpr->boolop == NOT_EXPR)
				{
					/* Skip, and do not keep track of the qual */
					uint32		previous_hash = context->qualid;
					uint32		previous_uniquequalnodeid = context->uniquequalid;

					context->qualid = 0;
					context->uniquequalid = 0;
					expression_tree_walker((Node *) boolexpr->args,
								pgqs_whereclause_tree_walker, context);
					context->qualid = previous_hash;
					context->uniquequalid = previous_uniquequalnodeid;
					return false;
				}
				else if (boolexpr->boolop == OR_EXPR)
				{
					context->qualid = 0;
					context->uniquequalid = 0;
				}
				else if (boolexpr->boolop == AND_EXPR)
				{
					context->uniquequalid = hashExpr((Expr *) boolexpr, context,
												pgqs_track_constants);
					context->qualid = hashExpr((Expr *) boolexpr, context, false);
				}
				expression_tree_walker((Node *) boolexpr->args,
								pgqs_whereclause_tree_walker, context);
				return false;
			}
		case T_OpExpr:
			pgqs_process_opexpr((OpExpr *) node, context);
			return false;
		case T_ScalarArrayOpExpr:
			pgqs_process_scalararrayopexpr((ScalarArrayOpExpr *) node, context);
			return false;
		case T_BooleanTest:
			pgqs_process_booltest((BooleanTest *) node, context);
			return false;
		default:
			expression_tree_walker(node, pgqs_whereclause_tree_walker, context);
			return false;
	}
}

/*
 * Calculate hash value for a key
 */
static uint32
pgqs_hash_fn(const void *key, Size keysize)
{
	const pgqsHashKey *k = (const pgqsHashKey *) key;

	return hash_uint32((uint32) k->userid) ^
		hash_uint32((uint32) k->dbid) ^
		hash_uint32((uint32) k->queryid) ^
		hash_uint32((uint32) k->uniquequalnodeid) ^
		hash_uint32((uint32) k->uniquequalid) ^
		hash_uint32((uint32) k->evaltype);
}

/*
 * Calculate hash value for a param
 */
static uint32
pgqs_hash_param_fn(const void *key, Size keysize)
{
	const pgqsParamKey *k = (const pgqsParamKey *) key;

	return hash_uint32((uint32) k->paramno);
}

int param_key_compare_fn(const void* lhs, const void* rhs, size_t count)
{
	if (((pgqsParamKey *) lhs)->paramno == ((pgqsParamKey *) rhs)->paramno) {
		return 0;
	}
	else
	{
		return 1;
	}
}

static void add_params_to_hash(List *nestParams)
{
	ListCell *lc;
	pgqsParamKey key;
	bool found;
	pgqsParamEntry *entry;
	foreach(lc, nestParams)
	{
		Node *node = (Node *) lfirst(lc);
		if (IsA(node, NestLoopParam))
		{
			NestLoopParam *nlparam = (NestLoopParam *) node;
			Var *var = nlparam->paramval;


			memset(&key, 0, sizeof(pgqsParamKey));
			key.paramno = nlparam->paramno;

			entry = (pgqsParamEntry *) hash_search(pgqs_paramhash, &key, HASH_ENTER,
											&found);
			entry->var = var;
			entry->key = key;
		}
	}
}

static void
pgqs_set_planstates(PlanState *planstate, pgqsWalkerContext *context)
{
	context->outer_tlist = NIL;
	context->inner_tlist = NIL;
	context->index_tlist = NIL;
	context->outer_planstate = NULL;
	context->inner_planstate = NULL;
	context->planstate = planstate;
	if (IsA(planstate, AppendState))
	{
		AppendState * appendstate = (AppendState *) planstate;
		if (appendstate->as_nplans > 0)
			context->outer_planstate = appendstate->appendplans[0];
	}
	else if (IsA(planstate, MergeAppendState))
	{
		MergeAppendState * mergeappendstate = (MergeAppendState *) planstate;
		if (mergeappendstate->ms_nplans > 0)
			context->outer_planstate = mergeappendstate->mergeplans[0];
	}
#if PG_VERSION_NUM < 140000
	else if (IsA(planstate, ModifyTableState))
	{
		context->outer_planstate = ((ModifyTableState *) planstate)->mt_plans[0];
	}
#endif
	else
		context->outer_planstate = outerPlanState(planstate);

	if (context->outer_planstate)
		context->outer_tlist = context->outer_planstate->plan->targetlist;
	else
		context->outer_tlist = NIL;

	if (IsA(planstate, SubqueryScanState))
		context->inner_planstate = ((SubqueryScanState *) planstate)->subplan;
	else if (IsA(planstate, CteScanState))
		context->inner_planstate = ((CteScanState *) planstate)->cteplanstate;
	else
		context->inner_planstate = innerPlanState(planstate);

	if (context->inner_planstate)
		context->inner_tlist = context->inner_planstate->plan->targetlist;
	else
		context->inner_tlist = NIL;
	/* index_tlist is set only if it's an IndexOnlyScan */
	if (IsA(planstate->plan, IndexOnlyScan))
		context->index_tlist = ((IndexOnlyScan *) planstate->plan)->indextlist;
#if PG_VERSION_NUM >= 90500
	else if (IsA(planstate->plan, ForeignScan))
		context->index_tlist = ((ForeignScan *) planstate->plan)->fdw_scan_tlist;
	else if (IsA(planstate->plan, CustomScan))
		context->index_tlist = ((CustomScan *) planstate->plan)->custom_scan_tlist;
#endif
	else
		context->index_tlist = NIL;
}

static Expr *
pgqs_resolve_var(Var *var, pgqsWalkerContext *context)
{
	List	   *tlist = NULL;
	PlanState  *planstate = context->planstate;

	pgqs_set_planstates(context->planstate, context);
	switch (var->varno)
	{
		case INNER_VAR:
			tlist = context->inner_tlist;
			break;
		case OUTER_VAR:
			tlist = context->outer_tlist;
			break;
		case INDEX_VAR:
			tlist = context->index_tlist;
			break;
		default:
			return (Expr *) var;
	}
	if (tlist != NULL)
	{
		TargetEntry *entry = get_tle_by_resno(tlist, var->varattno);

		if (entry != NULL)
		{
			Var		   *newvar = (Var *) (entry->expr);

			if (var->varno == OUTER_VAR)
				pgqs_set_planstates(context->outer_planstate, context);

			if (var->varno == INNER_VAR)
				pgqs_set_planstates(context->inner_planstate, context);

			var = (Var *) pgqs_resolve_var(newvar, context);
		}
	}

	Assert(!(IsA(var, Var) && IS_SPECIAL_VARNO(var->varno)));

	/* If the result is something OTHER than a var, replace it by a constexpr */
	if (!IsA(var, Var))
	{
		Const	   *consttext;

		consttext = (Const *) makeConst(TEXTOID, -1, -1, -1,
						CStringGetTextDatum(nodeToString(var)), false, false);
		var = (Var *) consttext;
	}

	pgqs_set_planstates(planstate, context);

	return (Expr *) var;
}

static uint32
hashExpr(Expr *expr, pgqsWalkerContext *context, bool include_const)
{
	StringInfo	buffer = makeStringInfo();

	exprRepr(expr, buffer, context, include_const);
	return hash_any((unsigned char *) buffer->data, buffer->len);

}

static void
exprRepr(Expr *expr, StringInfo buffer, pgqsWalkerContext *context, bool include_const)
{
	ListCell   *lc;

	if (expr == NULL)
		return;

	appendStringInfo(buffer, "%d-", expr->type);
	if (IsA(expr, Var))
		expr = pgqs_resolve_var((Var *) expr, context);

	switch (expr->type)
	{
		case T_List:
			foreach(lc, (List *) expr)
				exprRepr((Expr *) lfirst(lc), buffer, context, include_const);

			break;
		case T_OpExpr:
			{
				OpExpr	   *opexpr;

				opexpr = pgqs_get_canonical_opexpr((OpExpr *) expr, NULL);

				appendStringInfo(buffer, "%d", opexpr->opno);
				exprRepr((Expr *) opexpr->args, buffer, context, include_const);
				break;
			}
		case T_Var:
			{
				Var		   *var = (Var *) expr;

				RangeTblEntry *rte = list_nth(context->rtable, var->varno - 1);

				if (rte->rtekind == RTE_RELATION)
					appendStringInfo(buffer, "%d;%d", rte->relid, var->varattno);
				else
					appendStringInfo(buffer, "NORTE%d;%d", var->varno, var->varattno);
			}
			break;
		case T_BoolExpr:
			appendStringInfo(buffer, "%d", ((BoolExpr *) expr)->boolop);
			exprRepr((Expr *) ((BoolExpr *) expr)->args, buffer, context, include_const);
			break;
		case T_BooleanTest:
			if (include_const)
				appendStringInfo(buffer, "%d", ((BooleanTest *) expr)->booltesttype);

			exprRepr((Expr *) ((BooleanTest *) expr)->arg, buffer, context, include_const);
			break;
		case T_Const:
			if (include_const)
				get_const_expr((Const *) expr, buffer);
			else
				appendStringInfoChar(buffer, '?');

			break;
		case T_CoerceViaIO:
			exprRepr((Expr *) ((CoerceViaIO *) expr)->arg, buffer, context, include_const);
			appendStringInfo(buffer, "|%d", ((CoerceViaIO *) expr)->resulttype);
			break;
		case T_FuncExpr:
			appendStringInfo(buffer, "|%d(", ((FuncExpr *) expr)->funcid);
			exprRepr((Expr *) ((FuncExpr *) expr)->args, buffer, context, include_const);
			appendStringInfoString(buffer, ")");
			break;
		case T_MinMaxExpr:
			appendStringInfo(buffer, "|minmax%d(", ((MinMaxExpr *) expr)->op);
			exprRepr((Expr *) ((MinMaxExpr *) expr)->args, buffer, context, include_const);
			appendStringInfoString(buffer, ")");
			break;

		default:
			appendStringInfoString(buffer, nodeToString(expr));
	}
}

#if PG_VERSION_NUM < 90500
static uint32
pgqs_uint32_hashfn(const void *key, Size keysize)
{
	return ((pgqsQueryStringHashKey *) key)->queryid;
}
#endif