/*
 * route structures helping functions
 *
 * Copyright (C) 2001-2003 FhG Fokus
 *
 * This file is part of opensips, a free SIP server.
 *
 * opensips is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version
 *
 * opensips is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301  USA
 *
 * History:
 * --------
 *  2003-01-29  src_port introduced (jiri)
 *  2003-03-19  replaced all mallocs/frees w/ pkg_malloc/pkg_free (andrei)
 *  2003-04-12  FORCE_RPORT_T added (andrei)
 *  2003-10-02  added SET_ADV_ADDRESS & SET_ADV_PORT (andrei)
 *  2006-03-02  mk_action -> mk_action_2p and mk_action3 -> mk_action_3p;
 *              both functions take as extra param the cfg line (bogdan)
 *  2006-12-22  support for script and branch flags added (bogdan)
 */

/*!
 * \file
 * \brief SIP routing engine - structure helping functions
 */

#include  "route_struct.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <regex.h>

#include "sr_module.h"
#include "dprint.h"
#include "ip_addr.h"
#include "mem/mem.h"
#include "mem/shm_mem.h"
#include "ut.h" /* ZSW() */
#include "transformations.h"
#include "xlog.h"
#include "mod_fix.h" /* free_cmd_gparams (OT #601) */

struct expr* mk_exp(int op, struct expr* left, struct expr* right)
{
	struct expr * e;
	e=(struct expr*)pkg_malloc(sizeof (struct expr));
	if (e==0) goto error;
	e->type=EXP_T;
	e->op=op;
	e->left.v.expr=left;
	e->right.v.expr=right;
	return e;
error:
	LM_CRIT("pkg memory allocation failure\n");
	return 0;
}


struct expr* mk_elem(int op, int leftt, void *leftd, int rightt, void *rightd)
{
	struct expr * e;
	e=(struct expr*)pkg_malloc(sizeof (struct expr));
	if (e==0) goto error;
	memset(e, 0, sizeof(struct expr));
	e->type=ELEM_T;
	e->op=op;
	e->left.type    = leftt;
	e->left.v.data  = leftd;
	if((e->left.type==STR_ST || e->left.type==STRINGV_O)
			&& e->left.v.s.s!=NULL)
		e->left.v.s.len = strlen(e->left.v.s.s);
	e->right.type   = rightt;
	e->right.v.data = rightd;
	if((e->right.type==STR_ST || e->right.type==STRINGV_O)
			&& e->right.v.s.s!=0)
		e->right.v.s.len = strlen(e->right.v.s.s);
	return e;
error:
	LM_CRIT("pkg memory allocation failure\n");
	return 0;
}



struct action* mk_action(int type, int n, action_elem_t *elem,
														int line, char *file)
{
	int i;
	struct action* a;

	if(n>MAX_ACTION_ELEMS)
	{
		LM_ERR("too many action elements at %s:%d for %d",
			file, line, type);
		return 0;
	}

	a=(struct action*)pkg_malloc(sizeof(struct action));
	if (a==0) goto  error;
	memset(a,0,sizeof(struct action));
	a->type=type;

	for(i=0; i<n; i++)
	{
		a->elem[i].type = elem[i].type;
		a->elem[i].u.data = elem[i].u.data;
		if(a->elem[i].type==STR_ST && a->elem[i].u.s.s!=NULL)
			a->elem[i].u.s.len = strlen(a->elem[i].u.s.s);
	}

	a->line = line;
	a->file = file;
	a->next=0;
	return a;

error:
	LM_CRIT("pkg memory allocation failure\n");
	return 0;

}


struct action* append_action(struct action* a, struct action* b)
{
	struct action *t;
	if (b==0) return a;
	if (a==0) return b;

	for(t=a;t->next;t=t->next);
	t->next=b;
	return a;
}


/* OT (#601): deep tree free, see free_route_lists_deep().
 *
 * In "deep" mode the walk also releases what only exists in a fully
 * fix()'ed tree, so it may run ONLY on such trees (the route trees
 * dropped by a routes reload are always fully fixed):
 *  - the pv specs held by SCRIPTVAR elems/expr operands (pv_spec_free,
 *    vs a plain pkg_free of the shell in stock mode)
 *  - the regexes compiled by fix_expr() for =~ / !~ (RE_ST)
 *  - the per-command gparams of CMD_T / AMODULE_T actions (with their
 *    pv spec / pv elem model / fixup handle)
 *  - the xlog level struct (fixed xlog actions only)
 */
static void free_expr_r( struct expr *e, int deep)
{
	if (e==NULL)
		return;

	if (e->type==ELEM_T) {

		/* left ... */
		switch (e->left.type) {
			case EXPR_O:
				free_expr_r( e->left.v.expr, deep ); break;
			case ACTION_O:
				free_action_list_ex( (struct action*)e->left.v.data, deep ); break;
			case SCRIPTVAR_O:
				if (deep)
					pv_spec_free( (pv_spec_p)e->left.v.data );
				else
					pkg_free( e->left.v.data );
				break;
		}
		/* ... and right */
		switch (e->right.type) {
			case EXPR_ST:
				free_expr_r( e->right.v.expr, deep ); break;
			case ACTIONS_ST:
				free_action_list_ex( (struct action*)e->right.v.data, deep ); break;
			case SCRIPTVAR_ST:
				if (deep)
					pv_spec_free( (pv_spec_p)e->right.v.data );
				else
					pkg_free( e->right.v.data );
				break;
			case RE_ST:
				if (deep && e->right.v.data) {
					regfree( (regex_t*)e->right.v.data );
					pkg_free( e->right.v.data );
				}
				break;
		}

	} else if (e->type==EXP_T) {

		/* left ... */
		if (e->left.v.expr)
			free_expr_r( e->left.v.expr, deep );
		/* ... and right */
		if (e->right.v.expr)
			free_expr_r( e->right.v.expr, deep );

	}

	pkg_free( e );
}


static void free_action_elem_r( action_elem_t *e, int deep)
{
	if (e->type==EXPR_ST)
		free_expr_r( (struct expr*)e->u.data, deep );
	else if (e->type==ACTIONS_ST)
		free_action_list_ex( (struct action*)e->u.data, deep );
	else if (e->type==SCRIPTVAR_ST) {
		if (deep)
			pv_spec_free( (pv_spec_p)e->u.data );
		else
			pkg_free(e->u.data);
	}
	else if (e->type==SCRIPTVAR_ELEM_ST)
		pv_elem_free_all(e->u.data);
}


void free_action_list_ex( struct action *a, int deep)
{
	int i;

	if (a==NULL)
		return;

	if (a->type==ASYNC_T || a->type==LAUNCH_T)
		/* unref the resume route */
		unref_script_route
			( (struct script_route_ref*)(a->elem[1].u.data) );

	if (deep && (a->type==XLOG_T || a->type==XDBG_T)) {
		/* two-argument xlog(): elem[0] holds the log level
		 * (xl_level_t), allocated at fixup time and left as STR_ST,
		 * so free_action_elem() does not release it -- free it here */
		if (a->elem[0].type==STR_ST && a->elem[0].u.data) {
			xl_level_p xlp = (xl_level_p)a->elem[0].u.data;
			if (xlp->type==1) {
				if (xlp->v.sp.trans)
					free_transformation((trans_t*)xlp->v.sp.trans);
				if ((xlp->v.sp.pvp.pvv_flags & PV_PARAM_PVV_SHM) &&
						xlp->v.sp.pvp.pvv.s)
					shm_free(xlp->v.sp.pvp.pvv.s);
			}
			pkg_free(xlp);
			a->elem[0].u.data = NULL;
			a->elem[0].type = 0;
		}
	}

	if (deep && a->type==ROUTE_T && a->elem[2].type==SCRIPTVAR_ST) {
		/* route(name, params...): the grammar (cfg.y) stores the call
		   parameters in a separately pkg_malloc()'ed action_elem_t[]
		   (elem[1] = NUMBER_ST with the params count, elem[2] =
		   SCRIPTVAR_ST pointing at the array -- the type lies, it is
		   NOT a pv_spec, so the generic walk below must not treat it
		   as one). Its SCRIPTVAR_ST entries are pv specs to release;
		   strings are lexer-arena owned, numbers and NULLs own nothing */
		int nparams = (int)(long)a->elem[1].u.number;
		action_elem_t *params = (action_elem_t*)a->elem[2].u.data;
		if (params) {
			for( i=0 ; i<nparams && i<MAX_ACTION_ELEMS ; i++ )
				if (params[i].type==SCRIPTVAR_ST)
					pv_spec_free( (pv_spec_p)params[i].u.data );
			pkg_free(params);
			a->elem[2].u.data = NULL;
			a->elem[2].type = 0;
		}
	}

	if (deep && (a->type==CMD_T || a->type==AMODULE_T)) {
		/* fixed command actions hold one gparam per parameter in
		   elems[1..]; free them (and the tree-owned objects they point
		   to) here -- the generic elem walk below must not touch them */
		if (a->type==CMD_T)
			free_cmd_gparams(
				((const cmd_export_t*)a->elem[0].u.data_const)->params,
				a->elem);
		else
			free_cmd_gparams(
				((const acmd_export_t*)a->elem[0].u.data_const)->params,
				a->elem);
	} else {
		for( i=0 ; i<MAX_ACTION_ELEMS ; i++) {
			if (a->elem[i].type)
				free_action_elem_r( &a->elem[i], deep );
		}
	}

	if (a->next)
		free_action_list_ex(a->next, deep);

	pkg_free(a);
}

void free_action_list( struct action *a)
{
	free_action_list_ex( a, 0);
}



void print_expr(struct expr* exp)
{
	if (exp==0){
		LM_CRIT("null expression!\n");
		return;
	}
	if (exp->type==ELEM_T){
		switch(exp->left.type){
			case SCRIPTVAR_O:
				LM_GEN1(L_DBG, "scriptvar[%d]",
					(exp->left.v.spec)?exp->left.v.spec->type:0);
				break;
			case NUMBER_O:
			case NUMBERV_O:
				LM_GEN1(L_DBG, "%d",exp->left.v.n);
				break;
			case STRINGV_O:
				LM_GEN1(L_DBG, "\"%s\"", ZSW((char*)exp->left.v.data));
				break;
			case ACTION_O:
				break;
			case EXPR_O:
				print_expr((struct expr*)exp->left.v.data);
				break;
			default:
				LM_GEN1(L_DBG, "UNKNOWN[%d]", exp->left.type);
		}
		switch(exp->op){
			case EQUAL_OP:
				LM_GEN1(L_DBG, "==");
				break;
			case MATCHD_OP:
			case MATCH_OP:
				LM_GEN1(L_DBG, "=~");
				break;
			case NOTMATCHD_OP:
			case NOTMATCH_OP:
				LM_GEN1(L_DBG, "!~");
				break;
			case GT_OP:
				LM_GEN1(L_DBG, ">");
				break;
			case GTE_OP:
				LM_GEN1(L_DBG, ">=");
				break;
			case LT_OP:
				LM_GEN1(L_DBG, "<");
				break;
			case LTE_OP:
				LM_GEN1(L_DBG, "<=");
				break;
			case DIFF_OP:
				LM_GEN1(L_DBG, "!=");
				break;
			case PLUS_OP:
				LM_GEN1(L_DBG, "+");
				break;
			case MINUS_OP:
				LM_GEN1(L_DBG, "-");
				break;
			case DIV_OP:
				LM_GEN1(L_DBG, "/");
				break;
			case MULT_OP:
				LM_GEN1(L_DBG, "*");
				break;
			case MODULO_OP:
				LM_GEN1(L_DBG, " mod ");
				break;
			case BAND_OP:
				LM_GEN1(L_DBG, "&");
				break;
			case BOR_OP:
				LM_GEN1(L_DBG, "|");
				break;
			case BXOR_OP:
				LM_GEN1(L_DBG, "^");
				break;
			case BLSHIFT_OP:
				LM_GEN1(L_DBG, "<<");
				break;
			case BRSHIFT_OP:
				LM_GEN1(L_DBG, ">>");
				break;
			case BNOT_OP:
				LM_GEN1(L_DBG, "~");
				break;
			case VALUE_OP:
			case NO_OP:
				break;
			default:
				LM_GEN1(L_DBG, "<UNKNOWN[%d]>", exp->op);
		}
		switch(exp->right.type){
			case NOSUBTYPE:
					/* LM_GEN1(L_DBG, "N/A"); */
					break;
			case STRING_ST:
					LM_GEN1(L_DBG, "\"%s\"", ZSW((char*)exp->right.v.data));
					break;
			case NET_ST:
					print_net((struct net*)exp->right.v.data);
					break;
			case IP_ST:
					print_ip("", (struct ip_addr*)exp->right.v.data, "");
					break;
			case ACTIONS_ST:
					print_actions((struct action*)exp->right.v.data);
					break;
			case NUMBER_ST:
					LM_GEN1(L_DBG, "%d",exp->right.v.n);
					break;
			case SCRIPTVAR_ST:
					LM_GEN1(L_DBG, "scriptvar[%d]", exp->right.v.spec->type);
					break;
			case NULLV_ST:
					LM_GEN1(L_DBG, "null");
					break;
			case EXPR_ST:
					print_expr((struct expr*)exp->right.v.data);
					break;
			default:
					LM_GEN1(L_DBG, "type<%d>", exp->right.type);
		}
	}else if (exp->type==EXP_T){
		switch(exp->op){
			case AND_OP:
					LM_GEN1(L_DBG, "AND( ");
					print_expr(exp->left.v.expr);
					LM_GEN1(L_DBG, ", ");
					print_expr(exp->right.v.expr);
					LM_GEN1(L_DBG, " )");
					break;
			case OR_OP:
					LM_GEN1(L_DBG, "OR( ");
					print_expr(exp->left.v.expr);
					LM_GEN1(L_DBG, ", ");
					print_expr(exp->right.v.expr);
					LM_GEN1(L_DBG, " )");
					break;
			case NOT_OP:
					LM_GEN1(L_DBG, "NOT( ");
					print_expr(exp->left.v.expr);
					LM_GEN1(L_DBG, " )");
					break;
			case EVAL_OP:
					LM_GEN1(L_DBG, "EVAL( ");
					print_expr(exp->left.v.expr);
					LM_GEN1(L_DBG, " )");
					break;
			case PLUS_OP:
					LM_GEN1(L_DBG, "PLUS( ");
					print_expr(exp->left.v.expr);
					LM_GEN1(L_DBG, ", ");
					print_expr(exp->right.v.expr);
					LM_GEN1(L_DBG, " )");
					break;
			case MINUS_OP:
					LM_GEN1(L_DBG, "MINUS( ");
					print_expr(exp->left.v.expr);
					LM_GEN1(L_DBG, ", ");
					print_expr(exp->right.v.expr);
					LM_GEN1(L_DBG, " )");
					break;
			case DIV_OP:
					LM_GEN1(L_DBG, "DIV( ");
					print_expr(exp->left.v.expr);
					LM_GEN1(L_DBG, ", ");
					print_expr(exp->right.v.expr);
					LM_GEN1(L_DBG, " )");
					break;
			case MULT_OP:
					LM_GEN1(L_DBG, "MULT( ");
					print_expr(exp->left.v.expr);
					LM_GEN1(L_DBG, ", ");
					print_expr(exp->right.v.expr);
					LM_GEN1(L_DBG, " )");
					break;
			case MODULO_OP:
					LM_GEN1(L_DBG, "MODULO( ");
					print_expr(exp->left.v.expr);
					LM_GEN1(L_DBG, ", ");
					print_expr(exp->right.v.expr);
					LM_GEN1(L_DBG, " )");
					break;
			case BAND_OP:
					LM_GEN1(L_DBG, "BAND( ");
					print_expr(exp->left.v.expr);
					LM_GEN1(L_DBG, ", ");
					print_expr(exp->right.v.expr);
					LM_GEN1(L_DBG, " )");
					break;
			case BOR_OP:
					LM_GEN1(L_DBG, "BOR( ");
					print_expr(exp->left.v.expr);
					LM_GEN1(L_DBG, ", ");
					print_expr(exp->right.v.expr);
					LM_GEN1(L_DBG, " )");
					break;
			case BXOR_OP:
					LM_GEN1(L_DBG, "BXOR( ");
					print_expr(exp->left.v.expr);
					LM_GEN1(L_DBG, ", ");
					print_expr(exp->right.v.expr);
					LM_GEN1(L_DBG, " )");
					break;
			case BLSHIFT_OP:
					LM_GEN1(L_DBG, "BLSHIFT( ");
					print_expr(exp->left.v.expr);
					LM_GEN1(L_DBG, ", ");
					print_expr(exp->right.v.expr);
					LM_GEN1(L_DBG, " )");
					break;
			case BRSHIFT_OP:
					LM_GEN1(L_DBG, "BRSHIFT( ");
					print_expr(exp->left.v.expr);
					LM_GEN1(L_DBG, ", ");
					print_expr(exp->right.v.expr);
					LM_GEN1(L_DBG, " )");
					break;
			case BNOT_OP:
					LM_GEN1(L_DBG, "BNOT( ");
					print_expr(exp->left.v.expr);
					LM_GEN1(L_DBG, " )");
					break;
			default:
					LM_GEN1(L_DBG, "UNKNOWN_EXP[%d] ", exp->op);
		}

	}else{
		LM_ERR("unknown type\n");
	}
}


void print_action(struct action* t)
{
	switch(t->type){
		case ASSERT_T:
				LM_GEN1(L_DBG, "assert(");
				break;
		case DROP_T:
				LM_GEN1(L_DBG, "drop(");
				break;
		case LOG_T:
				LM_GEN1(L_DBG, "log(");
				break;
		case ERROR_T:
				LM_GEN1(L_DBG, "error(");
				break;
		case ROUTE_T:
				LM_GEN1(L_DBG, "route(");
				break;
		case EXEC_T:
				LM_GEN1(L_DBG, "exec(");
				break;
		case LEN_GT_T:
				LM_GEN1(L_DBG, "len_gt(");
				break;
		case IF_T:
				LM_GEN1(L_DBG, "if (");
				break;
		case WHILE_T:
				LM_GEN1(L_DBG, "while (");
				break;
		case CMD_T:
				LM_GEN1(L_DBG, " function_call(");
				break;
		case RETURN_T:
				LM_GEN1(L_DBG, "return(");
				break;
		case EXIT_T:
				LM_GEN1(L_DBG, "exit(");
				break;
		case SWITCH_T:
				LM_GEN1(L_DBG, "switch(");
				break;
		case CASE_T:
				LM_GEN1(L_DBG, "case(");
				break;
		case DEFAULT_T:
				LM_GEN1(L_DBG, "default(");
				break;
		case BREAK_T:
				LM_GEN1(L_DBG, "break(");
				break;
		case EQ_T:
				LM_GEN1(L_DBG, "assign(");
				break;
		default:
				LM_GEN1(L_DBG, "UNKNOWN(");
	}
	switch(t->elem[0].type){
		case STRING_ST:
				LM_GEN1(L_DBG, "\"%s\"", ZSW(t->elem[0].u.string));
				break;
		case NUMBER_ST:
				LM_GEN1(L_DBG, "%lu",t->elem[0].u.number);
				break;
		case SCRIPTVAR_ST:
				LM_GEN1(L_DBG, "scriptvar[%d]",t->elem[0].u.item->type);
				break;
		case IP_ST:
				print_ip("", (struct ip_addr*)t->elem[0].u.data, "");
				break;
		case EXPR_ST:
				print_expr((struct expr*)t->elem[0].u.data);
				break;
		case ACTIONS_ST:
				print_actions((struct action*)t->elem[0].u.data);
				break;
		case CMD_ST:
				LM_GEN1(L_DBG, "f<%s>",((const cmd_export_t*)t->elem[0].u.data_const)->name);
				break;
		case SOCKID_ST:
				LM_GEN1(L_DBG, "%d:%s:%d",
						((struct socket_id*)t->elem[0].u.data)->proto,
						ZSW(((struct socket_id*)t->elem[0].u.data)->name),
						((struct socket_id*)t->elem[0].u.data)->port
						);
				break;
		default:
				LM_GEN1(L_DBG, "type<%d>", t->elem[0].type);
	}
	if (t->type==IF_T) LM_GEN1(L_DBG, ") {");
	switch(t->elem[1].type){
		case NOSUBTYPE:
				break;
		case STRING_ST:
				LM_GEN1(L_DBG, ", \"%s\"", ZSW(t->elem[1].u.string));
				break;
		case NUMBER_ST:
				LM_GEN1(L_DBG, ", %lu",t->elem[1].u.number);
				break;
		case EXPR_ST:
				print_expr((struct expr*)t->elem[1].u.data);
				break;
		case ACTIONS_ST:
				print_actions((struct action*)t->elem[1].u.data);
				break;
		case SOCKID_ST:
				LM_GEN1(L_DBG, "%d:%s:%d",
						((struct socket_id*)t->elem[1].u.data)->proto,
						ZSW(((struct socket_id*)t->elem[1].u.data)->name),
						((struct socket_id*)t->elem[1].u.data)->port
						);
				break;
		default:
				LM_GEN1(L_DBG, ", type<%d>", t->elem[1].type);
	}
	if (t->type==IF_T && t->elem[2].type!=NOSUBTYPE) LM_GEN1(L_DBG, " } else { ");
	switch(t->elem[2].type){
		case NOSUBTYPE:
				break;
		case STRING_ST:
				LM_GEN1(L_DBG, ", \"%s\"", ZSW(t->elem[2].u.string));
				break;
		case NUMBER_ST:
				LM_GEN1(L_DBG, ", %lu",t->elem[2].u.number);
				break;
		case EXPR_ST:
				print_expr((struct expr*)t->elem[2].u.data);
				break;
		case ACTIONS_ST:
				print_actions((struct action*)t->elem[2].u.data);
				break;
		case SOCKID_ST:
				LM_GEN1(L_DBG, "%d:%s:%d",
					((struct socket_id*)t->elem[2].u.data)->proto,
					ZSW(((struct socket_id*)t->elem[2].u.data)->name),
					((struct socket_id*)t->elem[2].u.data)->port
					);
			break;
		default:
			LM_GEN1(L_DBG, ", type<%d>", t->elem[2].type);
	}
	if (t->type==IF_T) LM_GEN1(L_DBG, "}; ");
	else	LM_GEN1(L_DBG, "); ");

}

void print_actions(struct action* a)
{
	while(a) {
		print_action(a);
		a = a->next;
	}
}


static int is_mod_func_in_expr(struct expr *e, const char *name, int param_no)
{
	if (e->type==ELEM_T) {
		if (e->left.type==ACTION_O)
			if (is_mod_func_used((struct action*)e->right.v.data,name,param_no)==1)
				return 1;
	} else if (e->type==EXP_T) {
		if (e->left.v.expr && is_mod_func_in_expr(e->left.v.expr,name,param_no)==1)
			return 1;
		if (e->right.v.expr && is_mod_func_in_expr(e->right.v.expr,name,param_no)==1)
			return 1;
	}
	return 0;
}


int is_mod_func_used(struct action *a, const char *name, int param_no)
{
	const cmd_export_t *cmd;
	while(a) {
		if (a->type==CMD_T) {
			/* first param is the name of the function */
			cmd = (const cmd_export_t*)a->elem[0].u.data_const;
			if (strcasecmp(cmd->name, name)==0) {
				if (param_no==-1 ||
					(a->elem[param_no].type != NOSUBTYPE &&
					a->elem[param_no].type != NULLV_ST)) {
					LM_DBG("function %s found to be used in script\n",name);
					return 1;
				}

			}
		}

		/* follow all leads from actions/expressions than may have 
		 * sub-blocks of instructions */
		if (a->elem[0].type==ACTIONS_ST)
			if (is_mod_func_used((struct action*)a->elem[0].u.data,
			name,param_no)==1)
				return 1;
		if (a->elem[0].type==EXPR_ST)
			if (is_mod_func_in_expr((struct expr*)a->elem[0].u.data,
			name,param_no)==1)
				return 1;

		if (a->elem[1].type==ACTIONS_ST)
			if (is_mod_func_used((struct action*)a->elem[1].u.data,
			name,param_no)==1)
				return 1;
		if (a->elem[1].type==EXPR_ST)
			if (is_mod_func_in_expr((struct expr*)a->elem[1].u.data,
			name,param_no)==1)
				return 1;

		if (a->elem[2].type==ACTIONS_ST)
			if (is_mod_func_used((struct action*)a->elem[2].u.data,
			name,param_no)==1)
				return 1;
		if (a->elem[2].type==EXPR_ST)
			if (is_mod_func_in_expr((struct expr*)a->elem[2].u.data,
			name,param_no)==1)
				return 1;

		a = a->next;
	}

	return 0;
}

int is_mod_async_func_used(struct action *a, const char *name, int param_no)
{
	const acmd_export_t *acmd;

	for (; a; a=a->next) {
		if (a->type==ASYNC_T || a->type==LAUNCH_T) {
			acmd = ((struct action *)(a->elem[0].u.data))->elem[0].u.data_const;

			if (strcasecmp(acmd->name, name)==0) {
				if (param_no==-1 ||
					(((struct action *)(a->elem[0].u.data))->elem[param_no].type != NOSUBTYPE &&
					((struct action *)(a->elem[0].u.data))->elem[param_no].type != NULLV_ST)) {
					LM_DBG("function %s found to be used in script\n",name);
					return 1;
				}

			}
		}

		/* follow all leads from actions than may have 
		 * sub-blocks of instructions */
		if (a->elem[0].type==ACTIONS_ST)
				if (is_mod_async_func_used((struct action*)a->elem[0].u.data,
				name,param_no)==1)
					return 1;

		if (a->elem[1].type==ACTIONS_ST)
				if (is_mod_async_func_used((struct action*)a->elem[1].u.data,
				name,param_no)==1)
					return 1;

		if (a->elem[2].type==ACTIONS_ST)
				if (is_mod_async_func_used((struct action*)a->elem[2].u.data,
				name,param_no)==1)
					return 1;
	}

	return 0;
}
