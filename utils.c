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

