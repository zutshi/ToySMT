#pragma once

#include <stdint.h>

void* xmalloc(size_t size);
void xfree (void* p);
char* xstrdup(const char *s);

void die(const char* fmt, ...);
int* list_of_numbers_to_array (char *s, size_t array_size, size_t *parsed);
char* create_string_of_numbers_in_range(int begin, size_t size);
void set_bit(uint32_t *v, int bit);
void clear_bit(uint32_t *v, int bit);
void negate_all_elements_in_int_array(int *a);
size_t count_ints_in_array(int *a);
char *list_of_ints_to_str(int *a);
