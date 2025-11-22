#pragma once
#include <stdio.h>
#include <stdlib.h>
#define cprintf printf
void panic(const char *s) { printf("PANIC: %s\n", s); exit(1); }
