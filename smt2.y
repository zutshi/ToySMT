%{
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
// Boehm garbage collector:
#include <gc.h>

#include "ToySMT.h"

int yylex(void);
void yyerror(const char *);

%}

%union
{
	char* text;
	int i;
	struct expr* e;
}

%token T_L_PAREN T_R_PAREN T_UNDERSCORE T_DOT
%token T_SET_LOGIC T_SET_INFO T_DECLARE_FUN T_ASSERT T_CHECK_SAT T_GET_MODEL T_QF_BV T_BVNOT T_BVNEG
%token T_SMT_LIB_VERSION
%token T_NUMBER T_ID T_TEXT T_CONST T_BV_DEC_CONST
%token T_BOOL T_BITVEC
%token T_EQ T_NOT T_OR T_XOR T_AND T_BVXOR T_BVADD T_BVSUB
%token T_BVUGE T_BVULE T_BVUGT T_BVULT T_DISTINCT
%token T_WHITESPACE

%type <text> T_ID
%type <i> T_NUMBER
%type <i> T_BV_DEC_CONST
%type <i> unary_func
%type <e> expr
%type <e> expr_list
%type <e> T_CONST

%error-verbose

%%

file:	commandline file
	| commandline
	;

commandline: T_L_PAREN T_SET_LOGIC T_QF_BV T_R_PAREN
        | T_L_PAREN T_SET_INFO T_SMT_LIB_VERSION T_NUMBER T_DOT T_NUMBER T_R_PAREN
        | T_L_PAREN T_DECLARE_FUN T_ID T_L_PAREN T_R_PAREN T_BOOL T_R_PAREN
	{
		create_variable($3, TY_BOOL, 1, 0);
	}
        | T_L_PAREN T_DECLARE_FUN T_ID T_L_PAREN T_R_PAREN T_L_PAREN T_UNDERSCORE T_BITVEC T_NUMBER T_R_PAREN T_R_PAREN
	{
		create_variable($3, TY_BITVEC, $9, 0);
	}
        | T_L_PAREN T_ASSERT expr T_R_PAREN
	{
		create_assert($3);
	}
        | T_L_PAREN T_CHECK_SAT T_R_PAREN
	{
		check_sat();
	}
        | T_L_PAREN T_GET_MODEL T_R_PAREN
	{
		get_model();
	}
        ;

unary_func:
	T_NOT		{ $$=OP_NOT; }
	| T_BVNOT	{ $$=OP_BVNOT; }
	| T_BVNEG	{ $$=OP_BVNEG; }
	;

expr_list:	expr
		| expr_list expr
		{
			// this is important. provide left associativity:
			$2->next=$1;
			$$=$2;
		}
		;

expr:	T_ID
	{
		$$=GC_MALLOC_ATOMIC(sizeof(struct expr));
		$$->type=EXPR_ID;
		$$->id=$1;
	}
	| T_CONST
        | T_L_PAREN T_UNDERSCORE T_BV_DEC_CONST T_NUMBER T_R_PAREN
	{
		$$=create_const_expr($3, $4);
	}
        | T_L_PAREN unary_func expr T_R_PAREN
	{
		$$=create_unary_expr($2, $3);
	}
        | T_L_PAREN T_EQ expr expr T_R_PAREN
	{
		$$=create_bin_expr(OP_EQ, $3, $4);
	}
        | T_L_PAREN T_OR expr_list T_R_PAREN
	{
		$$=create_vararg_expr(OP_OR, $3);
	}
        | T_L_PAREN T_XOR expr_list T_R_PAREN
	{
		$$=create_vararg_expr(OP_XOR, $3);
	}
        | T_L_PAREN T_AND expr_list T_R_PAREN
	{
		$$=create_vararg_expr(OP_AND, $3);
	}
        | T_L_PAREN T_BVXOR expr_list T_R_PAREN
	{
		$$=create_vararg_expr(OP_BVXOR, $3);
	}
        | T_L_PAREN T_BVADD expr_list T_R_PAREN
	{
		$$=create_vararg_expr(OP_BVADD, $3);
	}
        | T_L_PAREN T_BVSUB expr_list T_R_PAREN
	{
		$$=create_vararg_expr(OP_BVSUB, $3);
	}
        | T_L_PAREN T_DISTINCT expr_list T_R_PAREN
	{
		$$=create_distinct_expr($3);
	}
        | T_L_PAREN T_BVUGE expr expr T_R_PAREN
	{
		$$=create_bin_expr(OP_BVUGE, $3, $4);
	}
        | T_L_PAREN T_BVULE expr expr T_R_PAREN
	{
		$$=create_bin_expr(OP_BVULE, $3, $4);
	}
        | T_L_PAREN T_BVUGT expr expr T_R_PAREN
	{
		$$=create_bin_expr(OP_BVUGT, $3, $4);
	}
        | T_L_PAREN T_BVULT expr expr T_R_PAREN
	{
		$$=create_bin_expr(OP_BVULT, $3, $4);
	}
        ;

%%

extern FILE* yyin;
extern int yylineno;

void yyerror(const char *s)
{
	fprintf(stderr, "bison error: %s at line %d\n", s, yylineno);
}

int main(int argc, char *argv[])
{
	FILE* input = fopen(argv[1], "r");
	if (input==NULL)
	{
		printf ("Cannot open input file\n");
		return 0;
	} 

	yyin = input;

	do 
	{
		yyparse();
	}
	while (feof(yyin)==0);
};

