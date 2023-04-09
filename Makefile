lex.yy.c: rho.l
    lex rho.l

lex.yy.c: rho.y
    yacc -d rho.y

rho: lex.yy.c lex.yy.c
    cc -Wall -o rho lex.yy.c lex.yy.c rho.c

clean:
    rm *.yy.c *.tab.*
