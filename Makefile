y.tab.c: rho.y
    yacc -d rho.y

lex.yy.c: rho.l
    lex rho.l

rho: y.tab.c lex.yy.c
    cc -Wall -o rho y.tab.c lex.yy.c rho.c

clean:
    rm *.tab.c *.tab.h *.yy.c
