%{
/* Example Bison grammar */
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

/* Lexical analyzer - minimal implementation */
int yylex(void) {
    return 0; /* EOF */
}

/* Error handler */
void yyerror(const char *s) {
    fprintf(stderr, "Parse error: %s\n", s);
}
