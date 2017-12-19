#include <stdarg.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include "ToySMT.h"
#include "utils.h"

struct expr* create_unary_expr(int t, struct expr* op)
{
	struct expr* rt=calloc(sizeof(struct expr), 1);
	rt->type=EXPR_UNARY;
	rt->expr_type=t;
	rt->op1=op;
	return rt;
};

struct expr* create_bin_expr(int t, struct expr* op1, struct expr* op2)
{
	struct expr* rt=calloc(sizeof(struct expr), 1);
	rt->type=EXPR_BINARY;
	rt->expr_type=t;
	rt->op1=op1;
	rt->op2=op2;
	return rt;
};

struct expr* create_const_expr(uint32_t c, int w)
{
	//printf ("%s(%d, %d)\n", __FUNCTION__, c, w);
	struct expr* rt=calloc(sizeof(struct expr), 1);
	rt->type=EXPR_CONST;
	rt->const_val=c;
	rt->const_width=w;
	return rt;
};

char* op_name(int op)
{
	switch (op)
	{
		case OP_NOT:	return "not";
		case OP_EQ:	return "=";
		case OP_OR:	return "or";
		case OP_XOR:	return "xor";
		case OP_AND:	return "and";

		case OP_BVNOT:	return "bvnot";
		case OP_BVNEG:	return "bvneg";
		case OP_BVXOR:	return "bvxor";
		case OP_BVADD:	return "bvadd";
		case OP_BVSUB:	return "bvsub";
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
	if (e->type==EXPR_UNARY)
	{
		printf ("(%s ", op_name(e->expr_type));
		print_expr(e->op1);
		printf (")");
		return;
	};
	if (e->type==EXPR_BINARY)
	{
		printf ("(%s ", op_name(e->expr_type));
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
	int internal; // 0/1, 1 for internal
	char* id; // name
	int var_no; // in SAT instance
	int width; // in bits, 1 for bool
	// TODO: uint64_t? bitmap?
	uint32_t val; // what we've got from from SAT-solver's results. 0/1 for Bool
	struct variable* next;
};

struct variable* vars=NULL;

char* false_true_s[2]={"false", "true"};

void dump_all_variables(int dump_internal)
{
	//for (struct variable* v=vars; v; v=v->next)
	//	printf ("type=%d id=%s width=%d val=0x%x\n", v->type, v->id, v->width, v->val);
	printf ("(model\n");
	for (struct variable* v=vars; v; v=v->next)
	{
		if (v->internal==1 && dump_internal==0)
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
		v=vars=calloc(sizeof(struct variable), 1);
		//printf ("%s() line %d\n", __FUNCTION__, __LINE__);
	}
	else
	{
		for (v=vars; v->next; v=v->next);
		v->next=calloc(sizeof(struct variable), 1);
		v=v->next;
		//printf ("%s() line %d\n", __FUNCTION__, __LINE__);
	};
	v->type=type;
	v->id=strdup(name);
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

struct variable* create_internal_variable(int type, int width)
{
	char tmp[128];
	snprintf (tmp, sizeof(tmp), "internal!%d", next_internal_var);
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

void add_line(const char *s)
{
	struct clause* c;

	if (clauses==NULL)
		c=clauses=calloc(sizeof(struct clause*), 1);
	else
	{
		for (c=clauses; c->next; c=c->next);
		c->next=calloc(sizeof(struct clause), 1);
		c=c->next;
	}

	c->c=strdup(s);
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
	char *tmp=malloc(len);
	snprintf (tmp, len, "c %s", s);

	add_line(tmp);
	free (tmp);
};

struct variable* generate_const(uint32_t val, int width)
{
	//printf ("%s(%d, %d)\n", __FUNCTION__, val, width);
	struct variable* rt=create_internal_variable(TY_BITVEC, width);
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
		die ("Error: type mismatch: 'not' takes bool expression in %s\n", v->id);

	struct variable* rt=create_internal_variable(TY_BOOL, 1);
	add_comment ("generate_NOT");
	add_Tseitin_NOT (rt->var_no, v->var_no);
	return rt;
};

struct variable* generate_BVNOT(struct variable* v)
{
	if (v->type!=TY_BITVEC)
		die ("Error: type mismatch: 'bvnot' takes bitvec expression in %s\n", v->id);

	struct variable* rt=create_internal_variable(TY_BITVEC, v->width);
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
		die ("Error: type mismatch: 'bvneg' takes bitvec expression in %s\n", v->id);

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

struct variable* generate_BVADD(struct variable* v1, struct variable* v2)
{
	assert(v1->type==TY_BITVEC);
	assert(v2->type==TY_BITVEC);
	assert(v1->width==v2->width);
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
	struct variable* rt=create_internal_variable(TY_BITVEC, v1->width);
	add_comment ("generate_BVSUB");

	// TODO make func?
	struct variable* always_false=create_internal_variable(TY_BOOL, 1);
	add_clause1(-always_false->var_no);

	int borrow=always_false->var_no;

	// the first full-subtractor could be half-subtractor, but we make things simple here
	for (int i=0; i<v1->width; i++)
	{
		struct variable* borrow_out=create_internal_variable(TY_BOOL, 1);
		add_FS(v1->var_no+i, v2->var_no+i, borrow, rt->var_no+i, borrow_out->var_no);
		// newly created borrow_out is a borrow_in for the next full-subtractor:
		borrow=borrow_out->var_no;
	};

	return rt;
};

struct variable* generate_XOR(struct variable* v1, struct variable* v2)
{
	assert(v1->type==TY_BOOL);
	assert(v2->type==TY_BOOL);
	struct variable* rt=create_internal_variable(TY_BOOL, 1);
	add_comment ("generate_XOR");
	add_Tseitin_XOR (v1->var_no, v2->var_no, rt->var_no);
	return rt;
};

struct variable* generate_BVXOR(struct variable* v1, struct variable* v2)
{
	assert(v1->type==TY_BITVEC);
	assert(v2->type==TY_BITVEC);
	assert(v1->width==v2->width);
	struct variable* rt=create_internal_variable(TY_BITVEC, v1->width);
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
	struct variable* rt=create_internal_variable(TY_BOOL, 1);
	add_comment ("generate_OR_list");
	char tmp[200]={0};
	char buf[16];
	// TODO make func like create_string_of_numbers_in_range
	for (int i=0; i<width; i++)
	{
		snprintf (buf, 16, "%d ", var+i);
		strncat(tmp, buf, 200);
	};
	//printf ("%s() tmp=%s\n", __FUNCTION__, tmp);
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
		return generate_NOT(generate_XOR(v1, v2));
	}
	else
	{
		assert(v1->width==v2->width);
		add_comment ("generate_EQ for two bitvectors");
		struct variable* t=generate_BVXOR(v1,v2);
		return generate_NOT(generate_OR_list(t->var_no, t->width));
	};
};

struct variable* generate_AND(struct variable* v1, struct variable* v2)
{
	struct variable* rt=create_internal_variable(TY_BOOL, 1);
	add_comment ("generate_AND");
	add_clause3 (-v1->var_no, -v2->var_no, rt->var_no);
	add_clause2 (v1->var_no, -rt->var_no);
	add_clause2 (v2->var_no, -rt->var_no);
	return rt;
};

struct variable* generate_OR(struct variable* v1, struct variable* v2)
{
	struct variable* rt=create_internal_variable(TY_BOOL, 1);
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

	if (e->type==EXPR_UNARY)
	{
		switch (e->expr_type)
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
		switch (e->expr_type)
		{
			case OP_EQ:	return generate_EQ (v1, v2);
			case OP_OR:	return generate_OR (v1, v2);
			case OP_XOR:	return generate_XOR (v1, v2);
			case OP_AND:	return generate_AND (v1, v2);
			case OP_BVXOR:	return generate_BVXOR (v1, v2);
			case OP_BVADD:	return generate_BVADD (v1, v2);
			case OP_BVSUB:	return generate_BVSUB (v1, v2);
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

int sat=0;

void check_sat()
{
	//printf ("%s()\n", __FUNCTION__);
	FILE* f=fopen ("tmp.cnf", "wt");
	assert (f!=NULL);
	fprintf (f, "p cnf %d %d\n", next_var_no-1, clauses_t);
	for (struct clause* c=clauses; c; c=c->next)
		fprintf (f, "%s\n", c->c);
	fclose (f);
	int rt=system ("minisat tmp.cnf result.txt > /dev/null");
	//printf ("rt=%d\n", rt);

	char buf[1024];

	f=fopen ("result.txt", "rt");
	fgets (buf, 1024, f);
	if (strncmp (buf, "SAT", 3)==0)
	{
		fgets (buf, 1024, f);
		//printf ("2nd line: %s\n", buf);
		char *t=strtok(buf, " \r\n");
		while (t!=NULL)
		{
			int v;
			assert (sscanf (t, "%d", &v)==1);
			if (v==0)
				break;
			struct variable* sv;
			if (v<0)
			{
				// don't do anything at all, "val" in all variable structures are cleared at start
			}
			else
			{
				sv=find_variable_by_no(v);
				// works for both bools and bitvecs:
				sv->val |= (1<<(v - sv->var_no));
			}
			t=strtok(NULL, " \r\n");
		}
		printf ("sat\n");
		sat=1;
	}
	else if (strncmp (buf, "UNSAT", 5)==0)
	{
		printf ("unsat\n");
		sat=0;
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
		dump_all_variables(0);
	else
		printf ("(error \"model is not available\")\n");
}

