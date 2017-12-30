#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdarg.h>
#include <assert.h>

#include <stdint.h>

// Boehm garbage collector:
#include <gc.h>

void die(const char* fmt, ...)
{
	va_list va;
	va_start (va, fmt);

	vprintf (fmt, va);
	exit(0);
};

void* xmalloc(size_t size)
{
	void* rt=malloc(size);
	if (rt==NULL)
		die ("Can't allocate %d bytes\n", size);
	memset(rt, 0, size);
	return rt;
};

void xfree (void* p)
{
	free(p);
};

char* xstrdup(const char *s)
{
	char* rt=xmalloc(strlen(s)+1);
	strcpy (rt, s);
	return rt;
};


// "1 2 3 4 5 -6" -> array of (signed) ints
// destroys input string
// allocates space for array
int* list_of_numbers_to_array (char *s, size_t array_size, size_t *parsed)
{
	int *rt=xmalloc(array_size*sizeof(int));
	assert(rt);
	int i=0;
	char *t=strtok(s, " \r\n");
	while (t!=NULL)
	{
		int v;
		assert (sscanf (t, "%d", &v)==1);
		rt[i++]=v;
		t=strtok(NULL, " \r\n");
	}
	*parsed=i;
	return rt;
};

char* create_string_of_numbers_in_range(int begin, size_t size)
{
	size_t buflen=size*10;
	char* buf=xmalloc(buflen);
	buf[0]=0;
	for (int i=0; i<size; i++)
	{
		char buf2[16];
		snprintf (buf2, sizeof(buf2), "%d ", begin+i);
		strncat(buf, buf2, buflen);
	};
	buf[strlen(buf)-1]=0;
	return buf;
};

void set_bit(uint32_t *v, int bit)
{
	(*v)|=1<<bit;
}

void clear_bit(uint32_t *v, int bit)
{
	(*v)&=~(1<<bit);
};

void negate_all_elements_in_int_array(int *a)
{
	for (int i=0; a[i]; i++)
		a[i]=-a[i];
};

size_t count_ints_in_array(int *a)
{
	int rt=0;
	for (int i=0; a[i]; i++)
		rt++;
	return rt;
};

char *list_of_ints_to_str(int *a)
{
	char* rt=malloc(count_ints_in_array(a)*10);
	rt[0]=0;
	char tmp[32];
	for (int i=0; a[i]; i++)
	{
		sprintf (tmp, "%d ", a[i]);
		strcat (rt, tmp);
	}
	rt[strlen(rt)-1]=0;
	//printf ("%s\n", rt);
	return rt;	
};


