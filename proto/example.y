%{
/* Example Bison grammar for Phoenix Exokernel protocol parsing */
#include <stdio.h>
#include <stdlib.h>

/* Forward declarations */
int yylex(void);
void yyerror(const char *s);
%}

%start input

%%

input :
    /* empty */
    ;

%%

/* Required functions for Bison parser */
int yylex(void) {
    return 0; /* End of input */
}

void yyerror(const char *s) {
    fprintf(stderr, "Parse error: %s\n", s);
}
