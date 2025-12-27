#pragma once

char getsuf(const char *s);
char *setsuf(char *s, char suf);
char *copy(const char *s);
int nodup(char *const *list, const char *s);
int callsys(const char *file, char *const argv[]);
