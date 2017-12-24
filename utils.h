#pragma once

void* xmalloc(size_t size);
void xfree (void* p);
char* xstrdup(const char *s);

void die(const char* fmt, ...);
int* list_of_numbers_to_array (char *s, size_t array_size, size_t *parsed);
char* create_string_of_numbers_in_range(int begin, size_t size);

