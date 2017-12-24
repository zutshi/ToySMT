#include <stdarg.h>
#include <stdio.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <unistd.h>
// Boehm garbage collector:
#include <gc.h>

#include "ToySMT.h"
#include "utils.h"

// global switches
bool dump_internal_variables;

// fwd decl:
void print_expr(struct expr* e);

struct expr* create_unary_expr(enum OP t, struct expr* op)
{
	struct expr* rt=GC_MALLOC(sizeof(struct expr));
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
	struct expr* rt=GC_MALLOC(sizeof(struct expr));
	memset (rt, 0, sizeof(struct expr));
	rt->type=EXPR_BINARY;
	rt->op=t;
	rt->op1=op1;
	rt->op2=op2;
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
/*
	printf ("%s(). input=\n", __FUNCTION__);
	for (struct expr* e=args; e; e=e->next)
	{
		print_expr(e);
		printf ("\n");
	};
*/
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
	struct expr* rt=GC_MALLOC(sizeof(struct expr));
	memset (rt, 0, sizeof(struct expr));
	rt->type=EXPR_CONST;
	rt->const_val=c;
	rt->const_width=w;
	return rt;
};

struct expr* create_zero_extend_expr(int bits, struct expr* e)
{
	struct expr* rt=GC_MALLOC(sizeof(struct expr));
	memset (rt, 0, sizeof(struct expr));
	rt->type=EXPR_ZERO_EXTEND;
	rt->const_val=bits;
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
		case OP_BVSUB:	return "bvsub";
		case OP_BVUGE:	return "bvuge";
		case OP_BVULE:	return "bvule";
		case OP_BVUGT:	return "bvugt";
		case OP_BVULT:	return "bvult";
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
	assert (0);
};

int next_var_no=1;

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
		v=vars=GC_MALLOC(sizeof(struct variable));
		//printf ("%s() line %d\n", __FUNCTION__, __LINE__);
	}
	else
	{
		for (v=vars; v->next; v=v->next);
		v->next=GC_MALLOC(sizeof(struct variable));
		v=v->next;
		//printf ("%s() line %d\n", __FUNCTION__, __LINE__);
	};
	v->type=type;
	v->id=strdup(name); // TODO replace strdup with something
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
	//printf ("%s() line %d variables=%p\n", __FUNCTION__, __LINE__, vars);
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

void add_line(const char *s)
{
	if (clauses==NULL)
		last_clause=clauses=GC_MALLOC(sizeof(struct clause));
	else
	{
		struct clause *cl=GC_MALLOC(sizeof(struct clause));
		last_clause->next=cl;
		last_clause=cl;
	};
	
	last_clause->c=strdup(s);

#if 0
	struct clause* c;

	if (clauses==NULL)
		c=clauses=GC_MALLOC_ATOMIC(sizeof(struct clause));
	else
	{
		for (c=clauses; c->next; c=c->next);
		c->next=GC_MALLOC_ATOMIC(sizeof(struct clause));
		c=c->next;
	}

	c->c=strdup(s);
#endif
}

void add_clause(const char* fmt, ...)
{
	va_list va;
	va_start (va, fmt);

	char buf[200];
	vsnprintf (buf, sizeof(buf), fmt, va);
	strcpy (buf+strlen(buf), " 0");

	//printf ("%s() %s\n", __FUNCTION__, buf);

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
	char *tmp=GC_MALLOC_ATOMIC(len);
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

	// TODO make func?
	struct variable* always_false=create_internal_variable("internal", TY_BOOL, 1);
	add_clause1(-always_false->var_no);

	struct variable *sum;
	struct variable *carry_out;
	generate_adder(v1, v2, always_false, &sum, &carry_out);
	return sum;
/*
	struct variable* rt=create_internal_variable(TY_BITVEC, v1->width);
	add_comment ("generate_BVADD");

	// TODO make func?
	struct variable* always_false=create_internal_variable(TY_BOOL, 1);
	add_clause1(-always_false->var_no);

	int carry=always_false->var_no;

	// the first full-adder could be half-adder, but we make things simple here
	for (int i=0; i<v1->width; i++)
	{
		struct variable* carry_out=create_internal_variable(TY_BOOL, 1);
		add_FA(v1->var_no+i, v2->var_no+i, carry, rt->var_no+i, carry_out->var_no);
		// newly created carry_out is a carry_in for the next full-adder:
		carry=carry_out->var_no;
	};

	return rt;
*/
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
	struct variable* rt=create_internal_variable("internal", TY_BITVEC, v1->width);
	add_comment ("generate_BVSUB");

	// TODO make func?
	struct variable* always_false=create_internal_variable("internal", TY_BOOL, 1);
	add_clause1(-always_false->var_no);

	int borrow=always_false->var_no;

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

	// TODO make func?
	struct variable* always_false=create_internal_variable("internal", TY_BOOL, 1);
	add_clause1(-always_false->var_no);

	int borrow=always_false->var_no;
	struct variable* borrow_out;

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
	//struct variable* rt=create_internal_variable(TY_BOOL, v1->width);
	add_comment (__FUNCTION__);

	//return generate_OR(generate_BVSUB_borrow(v1, v2), generate_EQ(v1, v2));
	//return generate_NOT(generate_BVSUB_borrow(v1, v2));
	return generate_BVSUB_borrow(v1, v2);
};

struct variable* generate_BVULE(struct variable* v1, struct variable* v2)
{
	assert(v1->type==TY_BITVEC);
	assert(v2->type==TY_BITVEC);
	assert(v1->width==v2->width);
	//struct variable* rt=create_internal_variable(TY_BOOL, v1->width);
	add_comment (__FUNCTION__);

	//return generate_OR(generate_BVSUB_borrow(v1, v2), generate_EQ(v1, v2));
	struct variable *v=generate_OR(generate_BVULT(v1, v2), generate_EQ(v1, v2));
	//printf ("%s() returns %s\n", __FUNCTION__, v->id);
	return v;
};

struct variable* generate_BVUGT(struct variable* v1, struct variable* v2)
{
	assert(v1->type==TY_BITVEC);
	assert(v2->type==TY_BITVEC);
	assert(v1->width==v2->width);
	//struct variable* rt=create_internal_variable(TY_BOOL, v1->width);
	add_comment (__FUNCTION__);

	return generate_BVSUB_borrow(v2, v1);
	//return generate_OR(generate_NOT(generate_BVSUB_borrow(v1, v2)), generate_EQ(v1, v2));
};

struct variable* generate_BVUGE(struct variable* v1, struct variable* v2)
{
	assert(v1->type==TY_BITVEC);
	assert(v2->type==TY_BITVEC);
	assert(v1->width==v2->width);
	//struct variable* rt=create_internal_variable(TY_BOOL, v1->width);
	add_comment (__FUNCTION__);

	struct variable *v=generate_OR(generate_BVUGT(v1, v2), generate_EQ(v1, v2));
	//printf ("%s() returns %s\n", __FUNCTION__, v->id);
	return v;
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
struct variable* generate_OR_list(int var, int width)
{
	//printf ("%s(%d, %d)\n", __FUNCTION__, var, width);
	struct variable* rt=create_internal_variable("internal", TY_BOOL, 1);
	add_comment ("generate_OR_list");
	char* tmp=create_string_of_numbers_in_range(var, width);
	add_clause("%s -%d", tmp, rt->var_no);
	for (int i=0; i<width; i++)
		add_clause2(-(var+i), rt->var_no);
	return rt;
};

struct variable* generate_EQ(struct variable* v1, struct variable* v2)
{
	//printf ("%s() v1=%d v2=%d\n", __FUNCTION__, v1->var_no, v2->var_no);
	if (v1->width==1)
	{
		assert(v2->width==1);
		add_comment ("generate_EQ");
		struct variable *v=generate_NOT(generate_XOR(v1, v2));
		//printf ("%s() returns %s (Bool)\n", __FUNCTION__, v->id);
		return v;
	}
	else
	{
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
/*
	add_clause3 (-v1->var_no, -v2->var_no, rt->var_no);
	add_clause2 (v1->var_no, -rt->var_no);
	add_clause2 (v2->var_no, -rt->var_no);
*/
	add_Tseitin_AND(v1->var_no, v2->var_no, rt->var_no);
	return rt;
};
/*    
# bit is 0 or 1.
    # i.e., if it's 0, output is 0 (all bits)
    # if it's 1, output=input
    def mult_by_bit(self, X, bit):
        return [self.AND(i, bit) for i in X]
*/

void add_Tseitin_mult_by_bit(int width, int var_no_in, int var_no_out, int var_no_bit)
{
	for (int i=0; i<width; i++)
		add_Tseitin_AND(var_no_in+i, var_no_bit, var_no_out+i);
};

struct variable* generate_mult_by_bit(struct variable *in, struct variable* bit)
{
	assert (in->type==TY_BITVEC);
	assert (bit->type==TY_BOOL);

	struct variable* rt=create_internal_variable("internal", TY_BITVEC, in->width);

	add_Tseitin_mult_by_bit(in->width, in->var_no, rt->var_no, bit->var_no);
	return rt;
};

// v1=v2 always!
void add_Tseitin_EQ(int v1, int v2)
{
	add_clause2 (-v1, v2);
	add_clause2 (v1, -v2);
}

void add_Tseitin_EQ_bitvecs(int width, int v1, int v2)
{
	for (int i=0; i<width; i++)
	{
		add_clause2 (-(v1+i), v2+i);
		add_clause2 (v1+i, -(v2+i));
	};
}

struct variable* generate_zero_extend(struct variable *in, int zeroes_to_add)
{
	int final_width=in->width+zeroes_to_add;
	struct variable* rt=create_internal_variable("internal", TY_BITVEC, final_width);

	// TODO: SOMETHING
	struct variable* always_false=create_internal_variable("always_false", TY_BOOL, 1);
	add_clause1(-always_false->var_no);

	add_Tseitin_EQ_bitvecs(in->width, in->var_no, rt->var_no);
	for (int i=0; i<zeroes_to_add; i++)
		add_Tseitin_EQ(rt->var_no+in->width, always_false->var_no);
	return rt;
};


/*
    # bit order: [MSB..LSB]
    # build multiplier using adders and mult_by_bit blocks:
    def multiplier(self, X, Y):
        assert len(X)==len(Y)
        out=[]
        #initial:
        prev=[self.const_false]*len(X)
        # first adder can be skipped, but I left thing "as is" to make it simpler
        for Y_bit in frolic.rvr(Y):
            s, carry = self.adder(self.mult_by_bit(X, Y_bit), prev)
            out.append(s[-1])
            prev=[carry] + s[:-1]
    
        return prev + frolic.rvr(out)
*/



struct variable* generate_BVMUL(struct variable* X, struct variable* Y)
{
	assert (X->type==TY_BITVEC);
	assert (Y->type==TY_BITVEC);
	assert (X->width==Y->width);
	int w=X->width;
#if 0
	assert (X->type==TY_BITVEC);
	assert (Y->type==TY_BITVEC);
	assert (X->width==Y->width);
	int w=X->width;

	// TODO make func?
	struct variable* always_false=create_internal_variable("always_false", TY_BOOL, 1);
	add_clause1(-always_false->var_no);

	struct variable* product=create_internal_variable("product", TY_BITVEC, w);
	struct variable* prev=create_internal_variable("prev", TY_BITVEC, w);
	// TODO func:
	for (int i=0; i<w; i++)
		add_Tseitin_EQ(prev->var_no+i, always_false->var_no);

/*
 10 = 1
10  = 2
110
*/
	for (int i=0; i<w; i++)
	{
		struct variable* partial_product=create_internal_variable("partial_product", TY_BITVEC, w);
		printf ("partial_product=%s\n", partial_product->id);
		generate_mult_by_bit(w, X->var_no, partial_product->var_no, Y->var_no+i);
		struct variable *sum;
		struct variable *carry;
		printf ("going to sum %s and %s\n", partial_product->id, prev->id);
		generate_adder(partial_product, prev, always_false /* carry_in */, &sum, &carry);
		printf ("sum=%s\n", sum->id);
		// LSB of sum:
		int LSB_var_no=sum->var_no+i;
		add_Tseitin_EQ(LSB_var_no, product->var_no+i);
		struct variable* new_prev=create_internal_variable("new_prev", TY_BITVEC, w);
		//add_Tseitin_EQ(new_prev->var_no+w-1, carry->var_no);
		for (int j=0; j<w-1; j++)
			add_Tseitin_EQ(new_prev->var_no+j, sum->var_no+j+1);
		printf ("new_prev=%s\n", new_prev->id);
		prev=new_prev;
	};
	return product;
#endif
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

	if (e->type==EXPR_UNARY)
	{
		switch (e->op)
		{
			case OP_NOT:	return generate_NOT (generate (e->op1));
			case OP_BVNOT:	return generate_BVNOT (generate (e->op1));
			case OP_BVNEG:	return generate_BVNEG (generate (e->op1));
			default:	assert(0);
		};
	};
	if (e->type==EXPR_BINARY)
	{
		struct variable* v1=generate(e->op1);
		struct variable* v2=generate(e->op2);
		switch (e->op)
		{
			case OP_EQ:	return generate_EQ (v1, v2);
			case OP_NEQ:	return generate_NEQ (v1, v2);
			case OP_OR:	return generate_OR (v1, v2);
			case OP_XOR:	return generate_XOR (v1, v2);
			case OP_AND:	return generate_AND (v1, v2);
			case OP_BVXOR:	return generate_BVXOR (v1, v2);
			case OP_BVADD:	return generate_BVADD (v1, v2);
			case OP_BVSUB:	return generate_BVSUB (v1, v2);
			case OP_BVMUL:	return generate_BVMUL (v1, v2);
			case OP_BVUGE:	return generate_BVUGE (v1, v2);
			case OP_BVULE:	return generate_BVULE (v1, v2);
			case OP_BVUGT:	return generate_BVUGT (v1, v2);
			case OP_BVULT:	return generate_BVULT (v1, v2);
			default:	assert(0);
		}
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

void check_sat()
{
	//printf ("%s()\n", __FUNCTION__);
	write_CNF ("tmp.cnf");

	unlink ("result.txt");
	int rt=system ("minisat tmp.cnf result.txt > /dev/null");
	if (rt==32512)
		die ("Error: minisat execitable not found. install it please.\n");

	// TODO parse_SAT_response()
	size_t buflen=next_var_no*10;
	char *buf=GC_MALLOC_ATOMIC(buflen);
	assert(buf);

	FILE* f=fopen ("result.txt", "rt");
	fgets (buf, buflen, f);
	if (strncmp (buf, "SAT", 3)==0)
	{
		fgets (buf, buflen, f);
		//printf ("2nd line: %s\n", buf);
		size_t total;	
		int *array=list_of_numbers_to_array(buf, next_var_no, &total);
		for (int i=0; array[i]; i++)
		{
			struct variable* sv;
			// works for both bools and bitvecs. set bit.
			int v=array[i];
			if (v<0)
			{
				sv=find_variable_by_no(-v);
				assert(sv);
				sv->val &= ~(1<<((-v) - sv->var_no));
			}
			else
			{
				sv=find_variable_by_no(v);
				assert(sv);
				sv->val |= (1<<(v - sv->var_no));
			}
		}
		printf ("sat\n");
		sat=true;
	}
	else if (strncmp (buf, "UNSAT", 5)==0)
	{
		printf ("unsat\n");
		sat=false;
	}
	else
	{
		die ("Fatal error. 1st line of minisat's answer unparsed: %s\n", buf);
	}
	fclose (f);
};

void get_model()
{
	if (sat)
		dump_all_variables(dump_internal_variables);
	else
		printf ("(error \"model is not available\")\n");
}

