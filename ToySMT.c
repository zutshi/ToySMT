#include <stdarg.h>
#include <stdio.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <unistd.h>

#include "ToySMT.h"
#include "utils.h"

#define VAR_ALWAYS_FALSE 1
#define VAR_ALWAYS_TRUE 2

struct variable* var_always_false=NULL;
struct variable* var_always_true=NULL;

// global switches
bool dump_internal_variables;

// fwd decl:
void print_expr(struct expr* e);

struct expr* create_unary_expr(enum OP t, struct expr* op)
{
	struct expr* rt=xmalloc(sizeof(struct expr));
	memset (rt, 0, sizeof(struct expr));
	rt->type=EXPR_UNARY;
	rt->op=t;
	rt->op1=op;
	return rt;
};

struct expr* create_bin_expr(enum OP t, struct expr* op1, struct expr* op2)
{
/*
	printf ("%s()\n", __FUNCTION__);
	printf ("op1=");
	print_expr(op1);
	printf ("\n");
	printf ("op2=");
	print_expr(op2);
	printf ("\n");
*/
	struct expr* rt=xmalloc(sizeof(struct expr));
	memset (rt, 0, sizeof(struct expr));
	rt->type=EXPR_BINARY;
	rt->op=t;
	rt->op1=op1;
	rt->op2=op2;
	return rt;
};

struct expr* create_ternary_expr(enum OP t, struct expr* op1, struct expr* op2, struct expr* op3)
{
/*
	printf ("%s()\n", __FUNCTION__);
	printf ("op1=");
	print_expr(op1);
	printf ("\n");
	printf ("op2=");
	print_expr(op2);
	printf ("\n");
*/
	struct expr* rt=xmalloc(sizeof(struct expr));
	rt->type=EXPR_TERNARY;
	rt->op=t;
	rt->op1=op1;
	rt->op2=op2;
	rt->op3=op3;
	return rt;
};

// from smt2.y:
int yylineno;

// fwd decl;
char* op_name(enum OP op);

struct expr* create_vararg_expr(enum OP t, struct expr* args)
{
/*
	printf ("%s(). input=\n", __FUNCTION__);
	for (struct expr* e=args; e; e=e->next)
	{
		print_expr(e);
		printf ("\n");
	};
*/

	// this provides left associativity.

	// be sure at least two expr in chain:
	if (args->next==NULL)
		die("line %d: '%s' requires 2 or more arguments!\n", yylineno, op_name(t));

	if (args->next->next==NULL)
		// only two expr in chain:
		return create_bin_expr(t, args->next, args);
	else
		// >2 expr in chain:
		return create_bin_expr(t, create_vararg_expr(t, args->next), args);
};

struct expr* create_distinct_expr(struct expr* args)
{
	// for 3 args:
	// and (a!=b, a!=c, b!=c)

	// be sure at least two expr in chain:
	if (args->next==NULL)
		die("line %d: 'distinct' requires 2 or more arguments!\n", yylineno);
	
	if (args->next->next==NULL)
		// only two expr in chain:
		return create_bin_expr (OP_NEQ, args->next, args);
	else
	{
		// >2 expr in chain:

		struct expr* e1=args;
		struct expr* big_AND_expr=NULL;
		for (struct expr* e2=args->next; e2; e2=e2->next)
		{
			struct expr* t=create_bin_expr (OP_NEQ, e1, e2);
			t->next=big_AND_expr;
			big_AND_expr=t;
		};
		// at this moment, big_AND_expr is chained expression of expr we will pass inside AND(...)
		struct expr *t=create_distinct_expr(args->next);
		t->next=big_AND_expr;
/*
		printf ("%s(). what we passing inside AND(...):\n", __FUNCTION__);
		print_expr(t);
		printf ("\n");
*/
		return create_vararg_expr(OP_AND, t);
	};
}

struct expr* create_const_expr(uint32_t c, int w)
{
	//printf ("%s(%d, %d)\n", __FUNCTION__, c, w);
	struct expr* rt=xmalloc(sizeof(struct expr));
	rt->type=EXPR_CONST;
	rt->const_val=c;
	rt->const_width=w;
	return rt;
};

struct expr* create_zero_extend_expr(int bits, struct expr* e)
{
	struct expr* rt=xmalloc(sizeof(struct expr));
	rt->type=EXPR_ZERO_EXTEND;
	rt->const_val=bits;
	rt->op1=e;
	return rt;
};

// get [start, end) bits
struct expr* create_extract_expr(unsigned end, unsigned start, struct expr* e)
{
	if (start>end)
		die ("line %d: start must be >=end, but you have start=%d, end=%d\n", yylineno, start, end);

	unsigned w=end-start+1;

	struct expr* rt=xmalloc(sizeof(struct expr));
	rt->type=EXPR_EXTRACT;
	rt->const_val=start;
	rt->const_width=w;
	rt->op1=e;
	return rt;
};

char* op_name(enum OP op)
{
	switch (op)
	{
		case OP_NOT:	return "not";
		case OP_EQ:	return "=";
		case OP_NEQ:	return "!="; // supported in SMT-LIB 2.x? not sure.
		case OP_OR:	return "or";
		case OP_XOR:	return "xor";
		case OP_AND:	return "and";

		case OP_BVNOT:	return "bvnot";
		case OP_BVNEG:	return "bvneg";
		case OP_BVXOR:	return "bvxor";
		case OP_BVADD:	return "bvadd";
		case OP_BVAND:	return "bvand";
		case OP_BVSUB:	return "bvsub";
		case OP_BVUGE:	return "bvuge";
		case OP_BVULE:	return "bvule";
		case OP_BVUGT:	return "bvugt";
		case OP_BVULT:	return "bvult";
		case OP_ITE:	return "ite";
		default:
			assert(0);
	};
};

void print_expr(struct expr* e)
{
	if (e->type==EXPR_ID)
	{
		printf ("%s", e->id);
		return;
	};
	if (e->type==EXPR_CONST)
	{
		printf ("%d (%d bits)", e->const_val, e->const_width);
		return;
	};
	if (e->type==EXPR_ZERO_EXTEND)
	{
		printf ("(ZEXT by %d bits: ", e->const_val);
		print_expr(e->op1);
		printf (")");
		return;
	};
	if (e->type==EXPR_EXTRACT)
	{
		printf ("(extract, start=%d width=%d bits: ", e->const_val, e->const_width);
		print_expr(e->op1);
		printf (")");
		return;
	};
	if (e->type==EXPR_UNARY)
	{
		printf ("(%s ", op_name(e->op));
		print_expr(e->op1);
		printf (")");
		return;
	};
	if (e->type==EXPR_BINARY)
	{
		printf ("(%s ", op_name(e->op));
		print_expr(e->op1);
		printf (" ");
		print_expr(e->op2);
		printf (")");
		return;
	};
	if (e->type==EXPR_TERNARY)
	{
		printf ("(%s ", op_name(e->op));
		print_expr(e->op1);
		printf (" ");
		print_expr(e->op2);
		printf (" ");
		print_expr(e->op3);
		printf (")");
		return;
	};
	assert (0);
};

// 3 instead of 1, becasue two variables (false/true) are allocated at start
int next_var_no=3;

struct variable
{
	int type; // TY_BOOL, TY_BITVEC
	bool internal; // 0/1, 1 for internal
	char* id; // name
	int var_no; // in SAT instance
	int width; // in bits, 1 for bool
	// TODO: uint64_t? bitmap?
	uint32_t val; // what we've got from from SAT-solver's results. 0/1 for Bool
	struct variable* next;
};

struct variable* vars=NULL;

char* false_true_s[2]={"false", "true"};

void dump_all_variables(bool dump_internal)
{
	//for (struct variable* v=vars; v; v=v->next)
	//	printf ("type=%d id=%s width=%d val=0x%x\n", v->type, v->id, v->width, v->val);
	printf ("(model\n");
	for (struct variable* v=vars; v; v=v->next)
	{
		if (v->internal==1 && dump_internal==false)
			continue; // skip internal variables

		if (v->type==TY_BOOL)
		{
			assert (v->val<=1);
			printf ("\t(define-fun %s () Bool %s)\n", v->id, false_true_s[v->val]);
		}
		else if (v->type==TY_BITVEC)
		{
  			printf ("\t(define-fun %s () (_ BitVec %d) (_ bv%u %d)) ; 0x%x\n",
				v->id, v->width, v->val, v->width, v->val);
  			//printf ("\t(define-fun %s () (_ BitVec %d) (_ bv%u %d)) ; 0x%x var_no=%d\n",
			//	v->id, v->width, v->val, v->width, v->val, v->var_no);
		}
		else
		{
			assert(0);
		};
	}
	printf (")\n");

};

struct variable* find_variable(char *id)
{
	if (vars==NULL)
		return NULL;
		
	for (struct variable* v=vars; v; v=v->next)
	{
		if (strcmp(id, v->id)==0)
			return v;
	};
	return NULL;
};

struct variable* find_variable_by_no(int no)
{
	if (vars==NULL)
		return NULL;
		
	for (struct variable* v=vars; v; v=v->next)
	{
		if (v->var_no == no)
			return v;
		if (no >= v->var_no && no < v->var_no+v->width)
			return v;
	};
	return NULL;
};

struct variable* create_variable(char *name, int type, int width, int internal)
{
	if (type==TY_BOOL)
		assert(width==1);

	//printf ("%s(%s, %d)\n", __FUNCTION__, name, type);
	//printf ("%s() line %d variables=%p\n", __FUNCTION__, __LINE__, vars);
	if (find_variable(name)!=NULL)
		die ("Fatal error: variable %s is already defined\n", name);

	struct variable* v;
	if (vars==NULL)
	{
		v=vars=xmalloc(sizeof(struct variable));
	}
	else
	{
		for (v=vars; v->next; v=v->next);
		v->next=xmalloc(sizeof(struct variable));
		v=v->next;
	};
	v->type=type;
	v->id=xstrdup(name); // TODO replace strdup with something
	if (type==TY_BOOL)
	{
		v->var_no=next_var_no;
		v->width=1;
		next_var_no++;
	}
	else if (type==TY_BITVEC)
	{
		v->var_no=next_var_no;
		v->width=width;
		next_var_no+=width;
	}
	else
		assert(0);
	//printf ("%s() %s var_no=%d\n", __FUNCTION__, name, v->var_no);
	v->internal=internal;
	return v;
}

int next_internal_var=1;

struct variable* create_internal_variable(char* prefix, int type, int width)
{
	char tmp[128];
	snprintf (tmp, sizeof(tmp), "%s!%d", prefix, next_internal_var);
	next_internal_var++;
	return create_variable(tmp, type, width, 1);
};

int clauses_t=0;

struct clause
{
	char *c;
	struct clause* next;
};

struct clause *clauses=NULL;
struct clause *last_clause=NULL;

void add_line(char *s)
{
	if (clauses==NULL)
		last_clause=clauses=xmalloc(sizeof(struct clause));
	else
	{
		struct clause *cl=xmalloc(sizeof(struct clause));
		last_clause->next=cl;
		last_clause=cl;
	};
	
	last_clause->c=s;
}

void add_clause(const char* fmt, ...)
{
	va_list va;
	va_start (va, fmt);

	size_t buflen=vsnprintf (NULL, 0, fmt, va)+2+1;
	char* buf=xmalloc(buflen);
	int written=vsnprintf (buf, buflen, fmt, va);
	assert (written<buflen);
	strcpy (buf+strlen(buf), " 0");

	add_line(buf);

	clauses_t++;
};

void add_clause1(int v1)
{
	add_clause ("%d", v1);
};

void add_clause2(int v1, int v2)
{
	add_clause ("%d %d", v1, v2);
};

void add_clause3(int v1, int v2, int v3)
{
	add_clause ("%d %d %d", v1, v2, v3);
};

void add_clause4(int v1, int v2, int v3, int v4)
{
	add_clause ("%d %d %d %d", v1, v2, v3, v4);
};

void add_comment(const char* s)
{
	//printf ("%s() %s\n", __FUNCTION__, s);

	size_t len=strlen(s)+3;
	char *tmp=xmalloc(len);
	snprintf (tmp, len, "c %s", s);

	add_line(tmp);
};

struct variable* generate_const(uint32_t val, int width)
{
	//printf ("%s(%d, %d)\n", __FUNCTION__, val, width);
	struct variable* rt=create_internal_variable("internal", TY_BITVEC, width);
	add_comment("generate_const()");
	for (int i=0; i<width; i++)
	{
		if ((val>>i)&1)
		{
			// add "always true" for this bit
			add_clause1 (rt->var_no+i);
		}
		else
		{
			// add "always false" for this bit
			add_clause1 (-(rt->var_no+i));
		}
	};
	return rt;
}

void add_Tseitin_NOT(int v1, int v2)
{
	add_clause2 (-v1, -v2);
	add_clause2 (v1, v2);
}

struct variable* generate_NOT(struct variable* v)
{
	if (v->type!=TY_BOOL)
		die ("Error: sort mismatch: 'not' takes bool expression, which is not in %s\n", v->id);

	struct variable* rt=create_internal_variable("internal", TY_BOOL, 1);
	add_comment ("generate_NOT");
	add_Tseitin_NOT (rt->var_no, v->var_no);
	return rt;
};

struct variable* generate_BVNOT(struct variable* v)
{
	if (v->type!=TY_BITVEC)
		die ("Error: sort mismatch: 'bvnot' takes bitvec expression, which is not in %s\n", v->id);

	struct variable* rt=create_internal_variable("internal", TY_BITVEC, v->width);
	add_comment ("generate_BVNOT");
	for (int i=0; i<v->width; i++)
		add_Tseitin_NOT (rt->var_no+i, v->var_no+i);
	return rt;
};

// fwd decl:
struct variable* generate_BVADD(struct variable* v1, struct variable* v2);

struct variable* generate_BVNEG(struct variable* v)
{
	if (v->type!=TY_BITVEC)
		die ("Error: sort mismatch: 'bvneg' takes bitvec expression, which is not in %s\n", v->id);

	add_comment ("generate_BVNEG");
	return generate_BVADD(generate_BVNOT(v), generate_const(1, v->width));
};

void add_Tseitin_XOR(int v1, int v2, int v3)
{
	add_clause3 (-v1, -v2, -v3);
	add_clause3 (v1, v2, -v3);
	add_clause3 (v1, -v2, v3);
	add_clause3 (-v1, v2, v3);
};

// TODO use Tseitin + gates?
// full-adder, as found by Mathematica using truth table:
void add_FA(int a, int b, int cin, int s, int cout)
{
	add_comment("add_FA");
        add_clause4(-a, -b, -cin, s);
        add_clause3(-a, -b, cout);
        add_clause3(-a, -cin, cout);
        add_clause3(-a, cout, s);
        add_clause4(a, b, cin, -s);
        add_clause3(a, b, -cout);
        add_clause3(a, cin, -cout);
        add_clause3(a, -cout, -s);
        add_clause3(-b, -cin, cout);
        add_clause3(-b, cout, s);
        add_clause3(b, cin, -cout);
        add_clause3(b, -cout, -s);
        add_clause3(-cin, cout, s);
        add_clause3(cin, -cout, -s);
};

void generate_adder(struct variable* a, struct variable* b, struct variable *carry_in, // inputs
	struct variable** sum, struct variable** carry_out) // outputs
{
	assert(a->type==TY_BITVEC);
	assert(b->type==TY_BITVEC);
	assert(a->width==b->width);

	assert(carry_in->type==TY_BOOL);

	*sum=create_internal_variable("adder_sum", TY_BITVEC, a->width);
	add_comment (__FUNCTION__);

	int carry=carry_in->var_no;

	// the first full-adder could be half-adder, but we make things simple here
	for (int i=0; i<a->width; i++)
	{
		*carry_out=create_internal_variable("adder_carry", TY_BOOL, 1);
		add_FA(a->var_no+i, b->var_no+i, carry, (*sum)->var_no+i, (*carry_out)->var_no);
		// newly created carry_out is a carry_in for the next full-adder:
		carry=(*carry_out)->var_no;
	};
};

struct variable* generate_BVADD(struct variable* v1, struct variable* v2)
{
	assert(v1->type==TY_BITVEC);
	assert(v2->type==TY_BITVEC);
	assert(v1->width==v2->width);

	struct variable *sum;
	struct variable *carry_out;
	generate_adder(v1, v2, var_always_false, &sum, &carry_out);
	return sum;
};

// TODO use Tseitin + gates?
// full-subtractor, as found by Mathematica using truth table:
void add_FS(int x, int y, int bin, int d, int bout)
{
	add_comment("add_FS");
	add_clause3(-bin, bout, -d);
	add_clause3(-bin, bout, -y);
	add_clause4(-bin, -d, -x, y);
	add_clause4(-bin, -d, x, -y);
	add_clause4(-bin, d, -x, -y);
	add_clause4(-bin, d, x, y);
	add_clause3(bin, -bout, d);
	add_clause3(bin, -bout, y);
	add_clause4(bin, -d, -x, -y);
	add_clause4(bin, -d, x, y);
	add_clause4(bin, d, -x, y);
	add_clause4(bin, d, x, -y);
	add_clause3(-bout, d, y);
	add_clause3(bout, -d, -y);
};

struct variable* generate_BVSUB(struct variable* v1, struct variable* v2)
{
	assert(v1->type==TY_BITVEC);
	assert(v2->type==TY_BITVEC);
	assert(v1->width==v2->width);
	struct variable* rt=create_internal_variable("SUB_result", TY_BITVEC, v1->width);
	add_comment ("generate_BVSUB");

	int borrow=VAR_ALWAYS_FALSE;

	// the first full-subtractor could be half-subtractor, but we make things simple here
	for (int i=0; i<v1->width; i++)
	{
		struct variable* borrow_out=create_internal_variable("internal", TY_BOOL, 1);
		add_FS(v1->var_no+i, v2->var_no+i, borrow, rt->var_no+i, borrow_out->var_no);
		// newly created borrow_out is a borrow_in for the next full-subtractor:
		borrow=borrow_out->var_no;
	};

	return rt;
};

// only borrow-out is returned!
// TODO join two functions into one?!
struct variable* generate_BVSUB_borrow(struct variable* v1, struct variable* v2)
{
	assert(v1->type==TY_BITVEC);
	assert(v2->type==TY_BITVEC);
	assert(v1->width==v2->width);
	struct variable* rt=create_internal_variable("internal", TY_BITVEC, v1->width);
	add_comment ("generate_BVSUB_borrow");

	int borrow=VAR_ALWAYS_FALSE;
	struct variable* borrow_out=NULL; // make compiler happy

	// the first full-subtractor could be half-subtractor, but we make things simple here
	for (int i=0; i<v1->width; i++)
	{
		borrow_out=create_internal_variable("internal", TY_BOOL, 1);
		add_FS(v1->var_no+i, v2->var_no+i, borrow, rt->var_no+i, borrow_out->var_no);
		// newly created borrow_out is a borrow_in for the next full-subtractor:
		borrow=borrow_out->var_no;
	};
	//printf ("%s() returns %s\n", __FUNCTION__, borrow_out->id);
	return borrow_out;
};

// fwd decl:
struct variable* generate_EQ(struct variable* v1, struct variable* v2);
struct variable* generate_OR(struct variable* v1, struct variable* v2);

struct variable* generate_BVULT(struct variable* v1, struct variable* v2)
{
	assert(v1->type==TY_BITVEC);
	assert(v2->type==TY_BITVEC);
	assert(v1->width==v2->width);
	add_comment (__FUNCTION__);

	return generate_BVSUB_borrow(v1, v2);
};

struct variable* generate_BVULE(struct variable* v1, struct variable* v2)
{
	assert(v1->type==TY_BITVEC);
	assert(v2->type==TY_BITVEC);
	assert(v1->width==v2->width);
	add_comment (__FUNCTION__);

	return generate_OR(generate_BVULT(v1, v2), generate_EQ(v1, v2));
};

struct variable* generate_BVUGT(struct variable* v1, struct variable* v2)
{
	assert(v1->type==TY_BITVEC);
	assert(v2->type==TY_BITVEC);
	assert(v1->width==v2->width);
	add_comment (__FUNCTION__);

	return generate_BVSUB_borrow(v2, v1);
};

struct variable* generate_BVUGE(struct variable* v1, struct variable* v2)
{
	assert(v1->type==TY_BITVEC);
	assert(v2->type==TY_BITVEC);
	assert(v1->width==v2->width);
	add_comment (__FUNCTION__);

	return generate_OR(generate_BVUGT(v1, v2), generate_EQ(v1, v2));
};

// fwd decl:
struct variable* generate_ITE(struct variable* sel, struct variable* t, struct variable* f);

// it's like SUBGE in ARM CPU in ARM mode
// rationale: used in divisor!
void generate_BVSUBGE(struct variable* enable, struct variable* v1, struct variable* v2,
	struct variable** output, struct variable** cond)
{
	assert(v1->type==TY_BITVEC);
	assert(v2->type==TY_BITVEC);
	assert(v1->width==v2->width);

	*cond=generate_BVUGE(v1, v2);
	struct variable *diff=generate_BVSUB(v1, v2);

	*output=generate_ITE(enable, generate_ITE(*cond, diff, v1), v1);
};

// fwd decl:
void add_Tseitin_OR_list(int var, int width, int var_out);
struct variable* generate_zero_extend(struct variable *in, int zeroes_to_add);

void add_Tseitin_BV_is_zero (int var_no, int width, int var_no_out)
{
	// all bits in BV are zero?

	//int tmp=next_var_no++; // allocate var
	struct variable *tmp=create_internal_variable("tmp", TY_BOOL, 1);
	add_Tseitin_OR_list(var_no, width, tmp->var_no);
	add_Tseitin_NOT(tmp->var_no, var_no_out);
};

// fwd decl
void add_Tseitin_EQ(int v1, int v2);
struct variable* generate_shift_left(struct variable* X, unsigned int cnt);
struct variable* generate_extract(struct variable *v, unsigned begin, unsigned width);
struct variable* generate_shift_right(struct variable* X, unsigned int cnt);

void generate_divisor (struct variable* divident, struct variable* divisor, struct variable** q, struct variable** r)
{
	assert (divident->type==TY_BITVEC);
	assert (divisor->type==TY_BITVEC);
	assert (divident->width==divisor->width);
	int w=divident->width;
	struct variable* wide1=generate_zero_extend(divisor, w);
	struct variable* wide2=generate_shift_left(wide1, w-1);

	*q=create_internal_variable("quotient", TY_BITVEC, w);

	for (int i=0; i<w; i++)
	{
		struct variable* enable=create_internal_variable("enable", TY_BOOL, 1);
		// enable is 1 if high part of wide2 is cleared
		add_Tseitin_BV_is_zero (wide2->var_no+w, w, enable->var_no);

		struct variable* cond;
		generate_BVSUBGE(enable, divident, generate_extract(wide2, 0, w), &divident, &cond);
		add_Tseitin_EQ(cond->var_no, (*q)->var_no+w-1-i);
		wide2=generate_shift_right(wide2, 1);
	};
	*r=divident;
};

struct variable* generate_BVUDIV(struct variable* v1, struct variable* v2)
{
	struct variable *q;
	struct variable *r;

	generate_divisor (v1, v2, &q, &r);

	return q;
};

struct variable* generate_BVUREM(struct variable* v1, struct variable* v2)
{
	struct variable *q;
	struct variable *r;

	generate_divisor (v1, v2, &q, &r);

	return r;
};

struct variable* generate_XOR(struct variable* v1, struct variable* v2)
{
	assert(v1->type==TY_BOOL);
	assert(v2->type==TY_BOOL);
	struct variable* rt=create_internal_variable("internal", TY_BOOL, 1);
	add_comment ("generate_XOR");
	add_Tseitin_XOR (v1->var_no, v2->var_no, rt->var_no);
	return rt;
};

// fwd decl:
void add_Tseitin_AND(int a, int b, int out);

struct variable* generate_BVAND(struct variable* v1, struct variable* v2)
{
	assert(v1->type==TY_BITVEC);
	assert(v2->type==TY_BITVEC);
	assert(v1->width==v2->width);
	struct variable* rt=create_internal_variable("AND_result", TY_BITVEC, v1->width);
	add_comment (__FUNCTION__);
	for (int i=0; i<v1->width; i++)
		add_Tseitin_AND (v1->var_no+i, v2->var_no+i, rt->var_no+i);
	return rt;
};

struct variable* generate_BVXOR(struct variable* v1, struct variable* v2)
{
	assert(v1->type==TY_BITVEC);
	assert(v2->type==TY_BITVEC);
	assert(v1->width==v2->width);
	struct variable* rt=create_internal_variable("internal", TY_BITVEC, v1->width);
	add_comment ("generate_BVXOR");
	for (int i=0; i<v1->width; i++)
		add_Tseitin_XOR (v1->var_no+i, v2->var_no+i, rt->var_no+i);
	return rt;
};

// as in Tseitin transformations.
// return=var OR var+1 OR ... OR var+width-1
void add_Tseitin_OR_list(int var, int width, int var_out)
{
	//printf ("%s(%d, %d)\n", __FUNCTION__, var, width);
	add_comment (__FUNCTION__);
	char* tmp=create_string_of_numbers_in_range(var, width);
	add_clause("%s -%d", tmp, var_out);
	for (int i=0; i<width; i++)
		add_clause2(-(var+i), var_out);
};

struct variable* generate_OR_list(int var, int width)
{
	//printf ("%s(%d, %d)\n", __FUNCTION__, var, width);
	struct variable* rt=create_internal_variable("internal", TY_BOOL, 1);
	add_comment (__FUNCTION__);
	add_Tseitin_OR_list(var, width, rt->var_no);
	return rt;
};

struct variable* generate_EQ(struct variable* v1, struct variable* v2)
{
	//printf ("%s() v1=%d v2=%d\n", __FUNCTION__, v1->var_no, v2->var_no);
	if (v1->type==TY_BOOL)
	{
		if(v2->type!=TY_BOOL)
		{
			printf ("%s() sort mismatch\n", __FUNCTION__);
			printf ("v1=%s type=%d width=%d\n", v1->id, v1->type, v1->width);
			printf ("v2=%s type=%d width=%d\n", v2->id, v2->type, v2->width);
			die("");
		};
		add_comment ("generate_EQ");
		struct variable *v=generate_NOT(generate_XOR(v1, v2));
		//printf ("%s() returns %s (Bool)\n", __FUNCTION__, v->id);
		return v;
	}
	else
	{
		assert (v2->type==TY_BITVEC);
		if(v1->width!=v2->width)
		{
			printf ("line %d. = can't work on bitvectors of different widths. you supplied %d and %d\n",
				yylineno, v1->width, v2->width);
			printf ("v1=%s, v2=%s\n", v1->id, v2->id);
			exit(0);
		};
		add_comment ("generate_EQ for two bitvectors");
		struct variable* t=generate_BVXOR(v1,v2);
		struct variable* v=generate_NOT(generate_OR_list(t->var_no, t->width));
		//printf ("%s() returns %s (bitvec %d)\n", __FUNCTION__, v->id, v->width);
		return v;
	};
};

struct variable* generate_NEQ(struct variable* v1, struct variable* v2)
{
	return generate_NOT(generate_EQ(v1,v2));
};

void add_Tseitin_AND(int a, int b, int out)
{
	add_clause3 (-a, -b, out);
	add_clause2 (a, -out);
	add_clause2 (b, -out);
};

struct variable* generate_AND(struct variable* v1, struct variable* v2)
{
	struct variable* rt=create_internal_variable("internal", TY_BOOL, 1);
	add_comment ("generate_AND");
	add_Tseitin_AND(v1->var_no, v2->var_no, rt->var_no);
	return rt;
};

void add_Tseitin_mult_by_bit(int width, int var_no_in, int var_no_out, int var_no_bit)
{
	for (int i=0; i<width; i++)
		add_Tseitin_AND(var_no_in+i, var_no_bit, var_no_out+i);
};
/*
struct variable* generate_mult_by_bit(struct variable *in, struct variable* bit)
{
	assert (in->type==TY_BITVEC);
	assert (bit->type==TY_BOOL);

	struct variable* rt=create_internal_variable("internal", TY_BITVEC, in->width);

	add_Tseitin_mult_by_bit(in->width, in->var_no, rt->var_no, bit->var_no);
	return rt;
};
*/
// v1=v2 always!
void add_Tseitin_EQ(int v1, int v2)
{
	add_clause2 (-v1, v2);
	add_clause2 (v1, -v2);
}

void add_Tseitin_EQ_bitvecs(int width, int v1, int v2)
{
	for (int i=0; i<width; i++)
		add_Tseitin_EQ(v1+i, v2+i);
}

struct variable* generate_zero_extend(struct variable *in, int zeroes_to_add)
{
	int final_width=in->width+zeroes_to_add;
	struct variable* rt=create_internal_variable("zero_extended", TY_BITVEC, final_width);

	add_Tseitin_EQ_bitvecs(in->width, in->var_no, rt->var_no);

	for (int i=0; i<zeroes_to_add; i++)
		add_clause1(-(rt->var_no + in->width + i));

	return rt;
};

void add_Tseitin_always_false(int v, int width)
{
	for (int i=0; i<width; i++)
		add_Tseitin_EQ(v+i, VAR_ALWAYS_FALSE);
};

// cnt is not a SMT variable!
struct variable* generate_shift_left(struct variable* X, unsigned int cnt)
{
	int w=X->width;

	struct variable* rt=create_internal_variable("shifted_left", TY_BITVEC, w);

	add_Tseitin_always_false(rt->var_no, cnt);
	add_Tseitin_EQ_bitvecs(w-cnt, rt->var_no+cnt, X->var_no);

	return rt;
};

// cnt is not a SMT variable!
struct variable* generate_shift_right(struct variable* X, unsigned int cnt)
{
	int w=X->width;

	struct variable* rt=create_internal_variable("shifted_right", TY_BITVEC, w);

	add_Tseitin_always_false(rt->var_no+w-1-cnt, cnt);
	add_Tseitin_EQ_bitvecs(w-cnt, rt->var_no, X->var_no+cnt);
	return rt;
};

struct variable* generate_extract(struct variable *v, unsigned begin, unsigned width)
{
	struct variable* rt=create_internal_variable("extracted", TY_BITVEC, width);
	for (int i=0; i<width; i++)
		add_Tseitin_EQ(rt->var_no+i, v->var_no+begin+i);

	return rt;
};

struct variable* generate_BVMUL(struct variable* X, struct variable* Y)
{
	assert (X->type==TY_BITVEC);
	assert (Y->type==TY_BITVEC);
	assert (X->width==Y->width);
	int w=X->width;
	int final_w=w*2;

	struct variable* X_extended=generate_zero_extend(X, w);

	struct variable* partial_products1[w]; // warning: GCC (?) extension
	struct variable* partial_products2[w]; // warning: GCC (?) extension

	for (int i=0; i<w; i++)
	{
		partial_products1[i]=create_internal_variable("partial_product1", TY_BITVEC, final_w);
		add_Tseitin_mult_by_bit(final_w, X_extended->var_no, partial_products1[i]->var_no, Y->var_no+i);
		partial_products2[i]=generate_shift_left(partial_products1[i], i);
	};

	struct variable *product=partial_products2[0];

	for (int i=1; i<w; i++)
		product=generate_BVADD(product, partial_products2[i]);

	return generate_extract(product, 0, w);
};

struct variable* generate_OR(struct variable* v1, struct variable* v2)
{
	struct variable* rt=create_internal_variable("internal", TY_BOOL, 1);
	add_comment ("generate_OR");
	add_clause3 (v1->var_no, v2->var_no, -rt->var_no);
	add_clause2 (-v1->var_no, rt->var_no);
	add_clause2 (-v2->var_no, rt->var_no);
	return rt;
};

// selector, true, false, x (output)
void add_Tseitin_ITE (int s, int t, int f, int x)
{
	add_comment (__FUNCTION__);
        // as found by my util 
        add_clause3(-s, -t, x);
        add_clause3(-s, t, -x);
        add_clause3(s, -f, x);
	add_clause3(s, f, -x);
};

struct variable* generate_ITE(struct variable* sel, struct variable* t, struct variable* f)
{
	assert (sel->type==TY_BOOL);
	assert (t->type==TY_BITVEC);
	assert (f->type==TY_BITVEC);
	assert (t->width==f->width);

	struct variable* rt=create_internal_variable("internal", TY_BITVEC, t->width);

	for (int i=0; i<t->width; i++)
		add_Tseitin_ITE(sel->var_no, t->var_no+i, f->var_no+i, rt->var_no+i);
	return rt;
}

struct variable* generate(struct expr* e)
{
/*
	printf ("%s() ", __FUNCTION__);
	print_expr(e);
	printf ("\n");
*/
	if (e->type==EXPR_ID)
	{
		struct variable* rt=find_variable(e->id);
		if(rt==NULL)
			die ("Variable %s hasn't been declared\n", e->id);
		//printf ("generate -> %d (by id %s)\n", rt->var_no, e->id);
		return rt;
	};

	if (e->type==EXPR_CONST)
	{
		//printf ("generate() const\n");
		return generate_const(e->const_val, e->const_width);
	};
	
	if (e->type==EXPR_ZERO_EXTEND)
	{
		return generate_zero_extend(generate(e->op1), e->const_val);
	};

	if (e->type==EXPR_EXTRACT)
	{
		return generate_extract(generate(e->op1), e->const_val, e->const_width);
	};

	if (e->type==EXPR_UNARY)
	{
		switch (e->op)
		{
			case OP_NOT:		return generate_NOT (generate (e->op1));
			case OP_BVNOT:		return generate_BVNOT (generate (e->op1));
			case OP_BVNEG:		return generate_BVNEG (generate (e->op1));
			case OP_BVSHL1:		return generate_shift_left (generate (e->op1), 1);
			case OP_BVSHR1:		return generate_shift_right (generate (e->op1), 1);
			default:		assert(0);
		};
	};
	if (e->type==EXPR_BINARY)
	{
		struct variable* v1=generate(e->op1);
		struct variable* v2=generate(e->op2);
		switch (e->op)
		{
			case OP_EQ:		return generate_EQ (v1, v2);
			case OP_NEQ:		return generate_NEQ (v1, v2);
			case OP_OR:		return generate_OR (v1, v2);
			case OP_XOR:		return generate_XOR (v1, v2);
			case OP_AND:		return generate_AND (v1, v2);
			case OP_BVXOR:		return generate_BVXOR (v1, v2);
			case OP_BVAND:		return generate_BVAND (v1, v2);
			case OP_BVADD:		return generate_BVADD (v1, v2);
			case OP_BVSUB:		return generate_BVSUB (v1, v2);
			case OP_BVMUL:		return generate_BVMUL (v1, v2);
			case OP_BVUGE:		return generate_BVUGE (v1, v2);
			case OP_BVULE:		return generate_BVULE (v1, v2);
			case OP_BVUGT:		return generate_BVUGT (v1, v2);
			case OP_BVULT:		return generate_BVULT (v1, v2);
			case OP_BVSUBGE:
						{
							struct variable *output;
							struct variable *cond;
							generate_BVSUBGE (var_always_true, v1, v2, &output, &cond);
							return output;
						};
			case OP_BVUDIV:		return generate_BVUDIV (v1, v2);
			case OP_BVUREM:		return generate_BVUREM (v1, v2);
			default:		assert(0);
		}
	};
	if (e->type==EXPR_TERNARY)
	{
		assert (e->op==OP_ITE);

		struct variable* sel=generate(e->op1);
		struct variable* t=generate(e->op2);
		struct variable* f=generate(e->op3);

		return generate_ITE(sel, t, f);
	};
	assert(0);
};

void create_assert (struct expr* e)
{
/*
	printf ("%s() ", __FUNCTION__);
	print_expr(e);
	printf ("\n");
*/
	struct variable* v=generate(e);
	add_comment ("create_assert()");
	add_clause1 (v->var_no); // v must be True
};

bool sat=false;

void write_CNF(char *fname)
{
	FILE* f=fopen (fname, "wt");
	assert (f!=NULL);
	fprintf (f, "p cnf %d %d\n", next_var_no-1, clauses_t);
	for (struct clause* c=clauses; c; c=c->next)
		fprintf (f, "%s\n", c->c);
	fclose (f);
};

void fill_variables_from_SAT_solver_response(int *array)
{
	for (int i=0; array[i]; i++)
	{
		struct variable* sv;
		// works for both bools and bitvecs. set bit.
		int v=array[i];

		// fixed to false/true, absent in our tables:
		if (abs(v)==1 || abs(v)==2)
			continue;
		if (v<0)
		{
			sv=find_variable_by_no(-v);
			assert(sv);
			clear_bit(&sv->val, (-v) - sv->var_no);
		}
		else
		{
			sv=find_variable_by_no(v);
			assert(sv);
			set_bit(&sv->val, v - sv->var_no);
		}
	}
};

int* solution;

bool run_SAT_solver_and_get_solution()
{
	write_CNF ("tmp.cnf");

	unlink ("result.txt");
	int rt=system ("minisat tmp.cnf result.txt > /dev/null");
	if (rt==32512)
		die ("Error: minisat execitable not found. install it please.\n");

	// parse SAT response:

	size_t buflen=next_var_no*10;
	char *buf=xmalloc(buflen);
	assert(buf);

	FILE* f=fopen ("result.txt", "rt");
	assert (fgets (buf, buflen, f)!=NULL);
	if (strncmp (buf, "SAT", 3)==0)
	{
		assert (fgets (buf, buflen, f)!=NULL);
		//printf ("2nd line: %s\n", buf);
		size_t total;
		// TODO make use of the fact that list is sorted!
		solution=list_of_numbers_to_array(buf, next_var_no, &total);
		fill_variables_from_SAT_solver_response(solution);
		fclose (f);
		return true;
	}
	else if (strncmp (buf, "UNSAT", 5)==0)
	{
		fclose (f);
		return false;
	}
	else if (strncmp (buf, "INDET", 5)==0)
	{
		printf ("minisat has been interrupted.\n");
		exit(0);
	}
	else
	{
		fclose (f);
		die ("Fatal error. 1st line of minisat's answer unparsed: %s\n", buf);
	}
	return false; // make compiler happy
};

void check_sat()
{
	if (run_SAT_solver_and_get_solution())
	{
		sat=true;
		printf ("sat\n");
	}
	else
	{
		sat=false;
		printf ("unsat\n");
	}
};

void get_model()
{
	if (sat)
		dump_all_variables(dump_internal_variables);
	else
		printf ("(error \"model is not available\")\n");
}

void get_all_models(bool dump_variables)
{
	int total=0;
	while (run_SAT_solver_and_get_solution())
	{
		total++;
		if (dump_variables)
			dump_all_variables(dump_internal_variables);
		// add negated solution:
		negate_all_elements_in_int_array(solution);
		char* str=list_of_ints_to_str(solution);
		add_clause(str);
	};
	printf ("Model count: %d\n", total);
};

void init()
{
	// TODO get rid of:
	add_clause1(-VAR_ALWAYS_FALSE);
	add_clause1(VAR_ALWAYS_TRUE);

	var_always_false=create_variable("always_false", TY_BOOL, 1, true);
	add_clause1(-var_always_false->var_no);
	var_always_true=create_variable("always_true", TY_BOOL, 1, true);
	add_clause1(var_always_true->var_no);
};

