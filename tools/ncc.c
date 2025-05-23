#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "compiler_utils.h"

int main(int argc, char *argv[])
{
    char *clist[50] = {0};
    char *llist[50] = {0};
    int nc = 0, nl = 0;
    int cflag = 0;
    for(int i = 1; i < argc; i++){
        if(strcmp(argv[i], "-c") == 0){
            cflag = 1;
        } else {
            char *t = copy(argv[i]);
            if(getsuf(t) == 'c'){
                clist[nc++] = t;
                llist[nl++] = setsuf(t, 'o');
            } else {
                if(nodup(llist, t))
                    llist[nl++] = t;
            }
        }
    }

    for(int i = 0; i < nc; i++){
        char *av[] = {"gcc", "-c", clist[i], NULL};
        if(callsys("/usr/bin/gcc", av)){
            fprintf(stderr, "compile failed: %s\n", clist[i]);
            return 1;
        }
    }

    if(!cflag && nl){
        int ac = 0;
        char *av[64];
        av[ac++] = "gcc";
        for(int i = 0; i < nl; i++)
            av[ac++] = llist[i];
        av[ac++] = NULL;
        if(callsys("/usr/bin/gcc", av))
            return 1;
    }
    return 0;
}
