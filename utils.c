#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdarg.h>
#include <assert.h>

void die(const char* fmt, ...)
{
	va_list va;
	va_start (va, fmt);

	vprintf (fmt, va);
	exit(0);
};

// "1 2 3 4 5 -6" -> array of (signed) ints
// destroys input string
// allocates space for array
int* list_of_numbers_to_array (char *s, size_t array_size, size_t *parsed)
{
	int *rt=malloc(array_size*sizeof(int));
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

