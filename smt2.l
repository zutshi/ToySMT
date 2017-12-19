%option yylineno

%{
#include "y.tab.h"
#include <stdlib.h>
#include <string.h>

#include "ToySMT.h"
// die():
#include "utils.h"

void yyerror(char *);
%}

%%

";".*         { /* single-line comment, do nothing */ }
"("           { return T_L_PAREN; }
")"           { return T_R_PAREN; }
"_"           { return T_UNDERSCORE; }
"."           { return T_DOT; }
"set-logic"   { return T_SET_LOGIC; }
"set-info"    { return T_SET_INFO; }
"declare-fun" { return T_DECLARE_FUN; }
"assert"      { return T_ASSERT; }
"check-sat"   { return T_CHECK_SAT; }
"get-model"   { return T_GET_MODEL; }
"Bool"        { return T_BOOL; }
"BitVec"      { return T_BITVEC; }
"="           { return T_EQ; }
"not"         { return T_NOT; }
"or"          { return T_OR; }
"xor"         { return T_XOR; }
"and"         { return T_AND; }
"bvnot"		{ return T_BVNOT; }
"bvneg"		{ return T_BVNEG; }
"bvxor"		{ return T_BVXOR; }
"bvadd"		{ return T_BVADD; }
"bvsub"		{ return T_BVSUB; }
"bvugt"		{ return T_BVUGT; }
"bvuge"		{ return T_BVUGE; }
"bvule"		{ return T_BVULE; }
"bvult"		{ return T_BVULT; }
"QF_BV"		{ return T_QF_BV; }
":smt-lib-version" { return T_SMT_LIB_VERSION; }
bv[0-9]+	{
			if (sscanf(yytext+2, "%d", &yylval.i)!=1)
				die ("Fatal error: can't parse %s as a decimal number\n", yytext);

			return T_BV_DEC_CONST;
		}
#x[0-9a-fA-F]+	{
			uint32_t val;
			if (sscanf(yytext+2, "%x", &val)!=1)
				die ("Fatal error: can't parse %s as a hexadecimal number\n", yytext);

			int width=strlen(yytext+2)*4;
			//printf ("%s:%d width=%d\n", __FUNCTION__, __LINE__, width);
			yylval.e=create_const_expr(val, width);
			return T_CONST;
		}

[a-zA-Z]+[a-zA-Z0-9]?  { yylval.text=strdup(yytext); return T_ID; }
[0-9]+		{
			if (sscanf(yytext, "%d", &yylval.i)!=1)
				die ("Fatal error: can't parse %s as a decimal number\n", yytext);

			return T_NUMBER;
		}



[ \n\r\t]       ;       /* skip whitespace */

.           printf("(lex/flex) unknown character: %c\n", yytext[0]);

%%

int yywrap(void)
{
	return 1;
}

void flex_set_str(char *s)
{
	YY_BUFFER_STATE buf;
	buf=yy_scan_string (s);
	yy_switch_to_buffer (buf);
};

void flex_cleanup()
{
	yy_delete_buffer( YY_CURRENT_BUFFER );
};

