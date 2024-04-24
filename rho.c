#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#include "list.h"
#include "rho.h"

#define PMAX       10
#define tag(p)     ((p)->tag)
#define bits32(x)  (32 - __builtin_clz(x))
#define max2(a, b) ((a) > (b) ? (a) : (b))
#define header(p)  ((rho_header *)((char *)(p) - sizeof(rho_header)))
#define len(p)     ((p) ? (header(p)->size - header(p)->avail) / sizeof(*(p)) : 0)
#define cap(p)     ((p) ? (header(p)->size / sizeof(*(p))) : 0)

#define toint(p)     ((p)->u.i)
#define tofloat(p)   ((p)->u.f)
#define toptr(p)     ((p)->u.ptr)
#define toany(p, t)  ((t)toptr(p))
#define tocproto(p)  toany(p, rho_cproto)
#define toproto(p)   toany(p, rho_proto *)
#define toclosure(p) toany(p, rho_closure *)

#define binop(ctx, op, sp)                                                     \
  do {                                                                         \
    rho_value *p = (sp)--;                                                     \
    switch (tag(sp)) {                                                         \
    case RHO_INT:                                                              \
      toint(sp) op## = rho_toint(rho_cast(ctx, p, RHO_INT));                   \
      break;                                                                   \
    case RHO_FLOAT:                                                            \
      tofloat(sp) op## = rho_tofloat(rho_cast(ctx, p, RHO_FLOAT));             \
      break;                                                                   \
    default:                                                                   \
      rho_panic(ctx, "runtime error: invalid operand(s)");                     \
    }                                                                          \
  } while (0)

#define binop_int(ctx, op, sp)                                                 \
  do {                                                                         \
    rho_value *p = (sp)--;                                                     \
    switch (tag(sp)) {                                                         \
    case RHO_INT:                                                              \
      toint(sp) op## = rho_toint(rho_cast(ctx, p, RHO_INT));                   \
      break;                                                                   \
    default:                                                                   \
      rho_panic(ctx, "runtime error: invalid operand(s)");                     \
    }                                                                          \
  } while (0)

typedef unsigned char byte;
typedef enum Op Op;
typedef enum Tk Tk;

#ifdef RHO_DEBUG
static int debug = 1;
#else
static int debug = 0;
#endif

enum Op {
  NOP,
  PSHC,
  PSHR,
  PSH,
  POP,
  BOP,
  CALL,
  RET,
  MAKE,
  ATTR,
};

static char *OP[] = {"nop", "pshc", "pshr", "psh",  "pop",
                     "bop", "call", "ret",  "make", "attr"};

enum Tk {
  EOT, /* end of token */
  CMT, /* // */

  INT, /* 114151 */
  FLT, /* 3.141592 */
  STR, /* "hello" */
  ID,  /* a */

  INC, /* ++ */
  DEC, /* -- */

  REV, /* ~ */
  NOT, /* ! */

  ADD, /* + */
  SUB, /* - */
  MUL, /* * */
  DIV, /* / */
  MOD, /* % */
  POW, /* ** */

  AND, /* & */
  OR,  /* | */
  XOR, /* ^ */

  LAND, /* && */
  LOR,  /* || */

  SHL, /* << */
  SHR, /* >> */

  EQ,  /* == */
  NEQ, /* != */

  ASS, /* = */

  PARL, /* ( */
  PARR, /* ) */
  COL,  /* : */
  SEM,  /* ; */
  DOT,  /* . */
  COM,  /* , */

  _kw,
  IF,   /* if */
  ELSE, /* else*/
  FOR,  /* for */
  BRK,  /* break */
  CTN,
  VAR,  /* var */
  FN,   /* fn */
  STRT, /* struct */
  _kwend,
};

static char *TK[] = {
    "EOT",   "//",       "INT", "FLT", "STR",    "ID",    "++", "--",   "~",
    "!",     "+",        "-",   "*",   "/",      "%",     "**", "&",    "|",
    "^",     "&&",       "||",  "<<",  ">>",     "==",    "!=", "=",    "(",
    ")",     ":",        ";",   ".",   ",",      "_kw",   "if", "else", "for",
    "break", "continue", "var", "fn",  "struct", "_kwend"};

static char *TG[] = {"int",      "float", "bool",    "pointer",
                     "c string", "proto", "c proto", "closure"};

static int precedence(int tk) {
  switch (tk) {
  case ADD:
  case SUB:
    return 11;
  case MUL:
  case DIV:
  case MOD:
  case POW:
    return 12;
  case OR:
    return 5;
  case XOR:
    return 6;
  case AND:
    return 7;
  case LAND:
    return 4;
  case LOR:
    return 3;
  case SHL:
  case SHR:
    return 10;
  case EQ:
  case NEQ:
    return 8;
  case ASS:
    return 1;
  default:
    return 0;
  }
}

struct rho_runtime {
  struct list_head ctx;
  rho_header *free[PMAX];
  rho_allocator alloc;
  int len;
};

struct rho_context {
  rho_runtime *r;
  rho_value *top;
  rho_value *sp;
  rho_ref *openrefs;
  rho_type *types;
  struct list_head link;
};

struct rho_header {
  rho_header *next;
  int refs;
  int size;
  int avail;
  void *ptr;
};

struct rho_string {
  byte *p;
  int len;
};

struct rho_ref {
  rho_ref *next;
  rho_value *vp;
  rho_value v;
};

struct rho_var {
  rho_type *type;
  rho_string name;
  int isconst : 1;
  int islocal : 1;
  int idx; /* index into proto::vars of the parent function if ::islocal,
              otherwise index into closure::refs of the parent function.  */
};

struct rho_type {
  rho_string name;
  rho_type **attr;
  int callable : 1;
  int alias;
};

struct rho_proto {
  rho_proto *prev;
  rho_proto **p;
  rho_var *vars;     /* arguments and local variables. */
  rho_var *refs;     /* closure variables. */
  rho_value *consts; /* constants */
  byte *code;
  int nin;  /* the number of arguments. */
  int nout; /* the number of values returned. */
};

struct rho_closure {
  rho_proto *p;
  rho_ref **refs;
};

struct token {
  int kind;
  int iskw : 1;
  int line;
  byte *linep;
  rho_string s;
};

/* An LL(1) parser */
struct rho_parser {
  rho_context *ctx;
  rho_proto *p;
  struct token t;
  struct token ahead;
  byte *src;
  byte *curp;
  byte *linep;
  int line;
  /* Members below are for debug only. */
  int n;
  byte op;
};

static int precedence(int);
static void next(rho_parser *);
static void peek(rho_parser *);
static void number(rho_parser *);
static void ident(rho_parser *);
static void stmt(rho_parser *);
static void stmtlist(rho_parser *);
static void vardecl(rho_parser *);
static void unexpr(rho_parser *);
static void expr(rho_parser *, int);
static void scan(rho_parser *, struct token *);
static void emit(rho_parser *, byte);
static void traceback(rho_context *);
static void closerefs(rho_context *, rho_value *);
static rho_ref *findref(rho_context *, rho_value *);
static rho_closure *makeclosure(rho_context *, rho_proto *, rho_ref **,
                                rho_value *);

rho_runtime *rho_new(rho_allocator alloc) {
  rho_runtime *r;
  rho_assert(alloc);
  if (!(r = alloc(0, sizeof(*r))))
    return NULL;
  r->alloc = alloc;
  r->len = 0;
  list_head_init(&r->ctx);
  return r;
}

static void inittypes(rho_context *ctx) {
  rho_type *tp;
  int sz;

  sz = 3 * sizeof(struct rho_type);
  tp = rho_allocgc(ctx, sz);
  memset(tp, 0, sz);
  tp[0].name.p = (byte *)TG[RHO_INT];
  tp[0].name.len = 3;
  tp[1].name.p = (byte *)TG[RHO_FLOAT];
  tp[1].name.len = 5;
  tp[2].name.p = (byte *)TG[RHO_BOOL];
  tp[2].name.len = 4;
  header(tp)->avail -= sz;
  ctx->types = tp;
}

rho_context *rho_open(rho_runtime *r, int size) {
  rho_context *ctx;

  rho_assert(r);
  if (!(ctx = r->alloc(0, size * sizeof(rho_value) + sizeof(*ctx))))
    return NULL;
  ctx->sp = (rho_value *)(ctx + 1);
  ctx->top = ctx->sp + size;
  ctx->openrefs = NULL;
  ctx->r = r;
  inittypes(ctx);
  rho_lock(ctx);
  list_add(&ctx->link, &r->ctx);
  r->len++;
  rho_unlock(ctx);
  return ctx;
}

void rho_close(rho_context *ctx) {
  rho_runtime *r;

  r = ctx->r;
  rho_lock(ctx);
  list_del(&ctx->link);
  r->len--;
  rho_unlock(ctx);
  // r->alloc(ctx->types, 0);
  r->alloc(ctx, 0);
}

/*
  Given a Rho context and the number of arguments pushed
  onto the stack, calls TOS-n, and then returns the number
  of values the callee pushes onto the stack.
 */
int rho_call(rho_context *ctx, int n) {
  rho_closure *cls;
  rho_value *sp, *bp, *ap;
  byte *pc, a;
  int k;

  sp = ctx->sp;
  bp = sp - n;
  ap = bp + 1;

  /* See if the callee is a C function. */
  if (tag(bp) == RHO_CPROTO)
    return tocproto(bp)(ctx, n);

  /* Make sure that the number of arguments given by caller
     is the same or more than that the callee needs if it
     is a Rho function. */
  cls = toclosure(bp);
  if (n < cls->p->nin)
    rho_panic(ctx, "runtime error: expected at least %d arguments",
              cls->p->nin);

  /* Allocate stack for local variables. */
  sp += len(cls->p->vars) - n;
  if (sp > ctx->top)
    rho_panic(ctx, "runtime error: stack overflow");

  /* Jump to the callee's bytecode. */
  pc = cls->p->code;

  /* Execution loop */
  for (;;) {
    switch (*pc++) {
    case CALL:
      ctx->sp = sp;
      k = rho_call(ctx, *pc++);
      sp = ctx->sp;
      if (sp - k < bp + n + k)
        rho_panic(ctx, "runtime error: expected more local variables");
      break;
    case RET:
      if (ctx->openrefs)
        closerefs(ctx, ap);
      k = *pc++;
      memmove(bp, sp - k + 1, k * sizeof(*sp));
      ctx->sp = bp + k - 1;
      return k;
    case MAKE:
      a = *pc++;
      switch (a) {
      case RHO_CLOSURE:
        *sp = rho_closure(makeclosure(ctx, toproto(sp), cls->refs, ap));
        break;
      default:
        rho_panic(ctx, "runtime error: bad object %d to make", a);
      }
      break;
    case PSHC:
      *++sp = cls->p->consts[*pc++];
      break;
    case PSH:
      *++sp = ap[*pc++];
      break;
    case POP:
      ap[*pc++] = *sp--;
    case BOP:
      a = *pc++;
      switch (a) {
      case ADD:
        binop(ctx, +, sp);
        break;
      case SUB:
        binop(ctx, -, sp);
        break;
      case MUL:
        binop(ctx, *, sp);
        break;
      case DIV:
        binop(ctx, /, sp);
        break;
      case MOD:
        binop_int(ctx, %, sp);
        break;
      case AND:
        binop_int(ctx, &, sp);
        break;
      case OR:
        binop_int(ctx, |, sp);
        break;
      case XOR:
        binop_int(ctx, ^, sp);
        break;
      case SHL:
        binop_int(ctx, <<, sp);
        break;
      case SHR:
        binop_int(ctx, >>, sp);
        break;
      }
      break;
    case NOP:
      break;
    default:
      rho_panic(ctx, "runtime error: bad opcode %d", *(pc - 1));
    }
  }
}

void rho_push(rho_context *ctx, rho_value v) { *++ctx->sp = v; }
rho_value rho_pop(rho_context *ctx) { return *ctx->sp--; }

static rho_closure *makeclosure(rho_context *ctx, rho_proto *p, rho_ref **encp,
                                rho_value *arg) {
  rho_closure *cls;
  rho_var *ref;
  int i, nrefs;

  nrefs = len(p->refs);
  cls = rho_allocex(ctx, rho_closure, nrefs);
  rho_assert(cls);
  cls->p = p;
  cls->refs = (rho_ref **)(cls + 1);
  for (i = 0; i < nrefs; i++) {
    ref = p->refs + i;
    if (ref->islocal)
      cls->refs[i] = findref(ctx, arg + ref->idx);
    else
      cls->refs[i] = encp[ref->idx];
  }
  return cls;
}

static rho_ref *findref(rho_context *ctx, rho_value *arg) {
  rho_ref *p, **pp;

  pp = &ctx->openrefs;
  while ((p = *pp) && p->vp >= arg) {
    if (p->vp == arg)
      return p;
    pp = &p->next;
  }
  p = rho_alloc(ctx, struct rho_ref);
  p->vp = arg;
  p->next = *pp;
  *pp = p;
  return p;
}

static void closerefs(rho_context *ctx, rho_value *arg) {
  rho_ref *p;

  p = ctx->openrefs;
  while (p && p->vp >= arg) {
    p->v = *p->vp;
    p->vp = &p->v;
    p = p->next;
    ctx->openrefs = p;
  }
}

#define expect(ps, tk)                                                         \
  do {                                                                         \
    if (ps->t.kind != tk)                                                      \
      rho_panic(ps->ctx, "parse error: expect token %s at line %d", TK[tk],    \
                ps->line);                                                     \
  } while (0)

static void stmtlist(rho_parser *ps) {
  Tk tk;

  while ((tk = ps->t.kind) != EOT)
    stmt(ps);
  emit(ps, RET);
  emit(ps, 1);
}

static void stmt(rho_parser *ps) {
  Tk tk;

  tk = ps->t.kind;
  switch (tk) {
  case CMT:
    next(ps);
    return;
  case IF:
    /* TODO: if statement */
    return;
  case FOR:
    /* TODO: for statement */
    return;
  case VAR:
    vardecl(ps);
    return;
  case FN:
    /* TODO: function declaration*/
    return;
  case STRT:
    /* TODO: struct declaration */
    return;
  default:
    expr(ps, 0); /* expression */
  }
}

static void pserror(rho_parser *ps, const char *s) {
  struct token *t;
  char *p, *end, *bp, b[64];
  int n, i;

  t = &ps->t;
  p = (char *)t->linep;
  end = (char *)t->s.p + t->s.len + 16;
  n = t->s.p - t->linep + 6;
  bp = b;

  bp += sprintf(bp, "%-2d |  ", t->line);
  while (p != end && *p != '\n') {
    bp += sprintf(bp, "%c", *p);
    p++;
  }
  *bp++ = '\n';
  for (i = 0; i < n; i++)
    *bp++ = ' ';
  *bp++ = '^';
  for (i = 0; i < t->s.len-1; i++)
    *bp++ = '~';
  *bp++ = '\n';
  for (i = 0; i < n; i++)
    *bp++ = ' ';
  *bp++ = '|';
  *bp++ = '\n';
  *bp++ = '\0';
  fprintf(stderr, b);
  fprintf(stderr, "parse error: ");
  rho_panic(ps->ctx, s);
}

/* arglist := ID [ ',' ID ] type */
static rho_type *arglist(rho_parser *ps, bool isconst) {
  rho_var v, *vp, **vpp;
  rho_type *tp;
  int n, i;

  expect(ps, ID);
  n = len(ps->p->vars);
  for (i = 0; i < n; i++) {
    vp = ps->p->vars + i;
    if (rho_strcmp(&vp->name, &ps->t.s) == 0)
      pserror(ps, "redundant variable declaration");
  }
  v.idx = i;
  v.isconst = isconst;
  v.name = ps->t.s;
  vpp = &ps->p->vars;
  *vpp = rho_append(ps->ctx, *vpp, &v, 1, rho_var);

  next(ps);
  switch (ps->t.kind) {
  case ID:
    n = len(ps->ctx->types);
    for (i = 0; i < n; i++) {
      tp = ps->ctx->types + i;
      if (rho_strcmp(&tp->name, &ps->t.s) == 0)
        return tp;
    }
    rho_panic(ps->ctx, "parse error: undefined type at line %d", ps->line);
  case COM:
    next(ps);
    tp = arglist(ps, isconst);
    if (tp)
      ps->p->vars[i].type = tp;
    return tp;
  default:
    rho_panic(ps->ctx, "parse error: unexpected token %s at line %d",
              TK[ps->t.kind], ps->line);
  }
}

/* vardecl := 'var' arglist */
static void vardecl(rho_parser *ps) {
  expect(ps, VAR);
  next(ps);
  arglist(ps, false);
  next(ps);
}

/* Top-down expression parsing. */
static void expr(rho_parser *ps, int plv) {
  Tk tk;
  int lv;

  tk = ps->t.kind;
  if (tk == EOT)
    return;

  unexpr(ps); /* left branch */
  tk = ps->t.kind;
  lv = precedence(tk);
  while (tk && plv < lv) {
    next(ps);
    expr(ps, lv); /* right branch */
    emit(ps, BOP);
    emit(ps, tk);
    tk = ps->t.kind;
    lv = precedence(tk);
  }
}

static void unexpr(rho_parser *ps) {
  Tk tk;

  tk = ps->t.kind;
  switch (tk) {
  case INT:
  case FLT:
    number(ps);
    return;
  case ID:
    /* TODO */
    ident(ps);
    return;
  case NOT:
  case REV:
    next(ps);
    expr(ps, 0);
    emit(ps, tk);
    return;
  case PARL:
    next(ps);
    expr(ps, 0);
    tk = ps->t.kind;
    if (tk != PARR)
      rho_panic(ps->ctx, "syntax error: un-closed parentheses at line %d",
                ps->line);
    next(ps);
    return;
  default:
    rho_panic(ps->ctx, "syntax error: unexpected token '%s' at line %d", TK[tk],
              ps->line);
  }
}

static void number(rho_parser *ps) {
  rho_value v, *vp, **vpp;
  int n, i;
  long k;
  double d;

  switch (ps->t.kind) {
  case INT:
    k = strtol((const char *)ps->t.s.p, NULL, 10);
    if (errno != 0)
      rho_panic(ps->ctx, "parse error: strtol failed with errno %d", errno);
    v = rho_int(k);
    break;
  case FLT:
    d = strtod((const char *)ps->t.s.p, NULL);
    if (errno != 0)
      rho_panic(ps->ctx, "parse error: strtod failed with errno %d", errno);
    v = rho_float(d);
    break;
  }

  n = len(ps->p->consts);
  for (i = 0; i < n; i++) {
    vp = ps->p->consts + i;
    if (rho_eq(ps->ctx, vp, &v))
      goto end;
  }
  vpp = &ps->p->consts;
  if (i == n)
    *vpp = rho_append(ps->ctx, *vpp, &v, 1, rho_value);
end:
  emit(ps, PSHC);
  emit(ps, i);
  next(ps);
}

static void ident(rho_parser *ps) {
  struct token *t;
  rho_var v, *vp, **vpp;
  rho_proto *p;
  int n, i, scope;

  t = &ps->t;
  scope = 0;
  for (p = ps->p; p; p = p->prev) {
    vpp = &p->refs;
    n = len(*vpp);
    for (i = 0; i < n; i++) {
      vp = p->refs + i;
      if (rho_strcmp(&t->s, &vp->name) == 0)
        goto end;
    }
    vpp = &p->vars;
    n = len(*vpp);
    for (i = 0; i < n; i++) {
      vp = p->vars + i;
      if (rho_strcmp(&t->s, &vp->name) == 0)
        goto end;
    }
    scope++;
  }
  rho_panic(ps->ctx, "parse error: undefined variable at line %d", ps->line);

end:
  v = *vp;
  v.islocal = scope > 1 ? false : true;
  if (scope == 0) {
    emit(ps, PSH);
  } else {
    *vpp = rho_append(ps->ctx, *vpp, &v, 1, rho_var);
    emit(ps, PSHR);
  }
  emit(ps, v.idx);
  next(ps);
}

static void peek(rho_parser *ps) { scan(ps, &ps->ahead); }

static void next(rho_parser *ps) {
  if (ps->ahead.kind == -1) {
    scan(ps, &ps->t);
    return;
  }
  ps->t = ps->ahead;
  ps->ahead.kind = -1;
}

void kw(struct token *t) {
  int i;

  if (t->s.len < 2)
    return;
  for (i = _kw + 1; i < _kwend; i++) {
    if (strncmp(TK[i], (const char *)t->s.p, t->s.len) == 0) {
      t->iskw = true;
      t->kind = i;
      return;
    }
  }
}

#define choose(ps, t, p, c, t1, t2)                                            \
  do {                                                                         \
    if (*(p) != c)                                                             \
      (t)->kind = t2;                                                          \
    else {                                                                     \
      (t)->kind = t1;                                                          \
      (p)++;                                                                   \
    }                                                                          \
    (t)->linep = (ps)->linep;                                                  \
    (t)->line = (ps)->line;                                                    \
  } while (0)

static void scan(rho_parser *ps, struct token *t) {
  byte *p, *pp;
  Tk tk;

  p = ps->curp;

top:
  switch (*p++) {
  case '\0':
    t->kind = EOT;
    goto defer;
  case '\n':
    ps->line++;
    ps->linep = p;
    goto top;
  case ' ':
  case '\t':
  case '\r':
    goto top;
  case '/':
    switch (*p) {
    case '/':
      pp = ++p;
      while (*p != '\n')
        p++;
      t->s.p = pp;
      t->s.len = p - pp;
      t->linep = ps->linep;
      t->line = ps->line;
      t->kind = CMT;
      break;
    case '*':
      pp = ++p;
      while (*p != '*' || *(p + 1) != '/') {
        if (*p == '\n')
          ps->line++;
        p++;
      }
      p += 2;
      t->s.p = pp;
      t->s.len = p - pp;
      t->linep = ps->linep;
      t->line = ps->line;
      t->kind = CMT;
      break;
    default:
      t->kind = DIV;
      t->linep = ps->linep;
      t->line = ps->line;
    }
    goto defer;
  case '*':
    choose(ps, t, p, '*', POW, MUL);
    goto defer;
  case '-':
    choose(ps, t, p, '-', DEC, SUB);
    goto defer;
  case '+':
    choose(ps, t, p, '+', INC, ADD);
    goto defer;
  case '%':
    t->kind = MOD;
    goto defer;
  case '&':
    choose(ps, t, p, '&', LAND, AND);
    goto defer;
  case '|':
    choose(ps, t, p, '|', LOR, OR);
    goto defer;
  case '<':
    if (*p != '<')
      goto err;
    p++;
    t->kind = SHL;
    t->linep = ps->linep;
    t->line = ps->line;
    goto defer;
  case '>':
    if (*p != '>')
      goto err;
    p++;
    t->kind = SHR;
    t->linep = ps->linep;
    t->line = ps->line;
    goto defer;
  case '^':
    t->kind = XOR;
    t->linep = ps->linep;
    t->line = ps->line;
    goto defer;
  case '~':
    t->kind = REV;
    t->linep = ps->linep;
    t->line = ps->line;
    goto defer;
  case '!':
    choose(ps, t, p, '=', NEQ, NOT);
    goto defer;
  case '=':
    choose(ps, t, p, '=', EQ, ASS);
    goto defer;
  case '(':
    t->kind = PARL;
    t->linep = ps->linep;
    t->line = ps->line;
    goto defer;
  case ')':
    t->kind = PARR;
    t->linep = ps->linep;
    t->line = ps->line;
    goto defer;
  case ':':
    t->kind = COL;
    t->linep = ps->linep;
    t->line = ps->line;
    goto defer;
  case ';':
    t->kind = SEM;
    t->linep = ps->linep;
    t->line = ps->line;
    goto defer;
  case '.':
    t->kind = DOT;
    t->linep = ps->linep;
    t->line = ps->line;
    goto defer;
  case ',':
    t->kind = COM;
    t->linep = ps->linep;
    t->line = ps->line;
    goto defer;
  case '"':
    pp = p;
    while (*p != '"' && *p != '\0')
      p++;
    t->s.p = pp;
    t->s.len = p - pp;
    t->linep = ps->linep;
    t->line = ps->line;
    t->kind = STR;
    p++;
    goto defer;
  default:
    if (isdigit(*(p - 1))) {
      pp = p - 1;
      tk = INT;
      while (isxdigit(*p) || *p == '.') {
        if (*p == '.')
          tk = FLT;
        p++;
      }
      t->s.p = pp;
      t->s.len = p - pp;
      t->linep = ps->linep;
      t->line = ps->line;
      t->kind = tk;
      goto defer;
    }
    if (isalpha(*(p - 1)) || *(p - 1) == '_') {
      pp = p - 1;
      while (isalpha(*p) || *p == '_')
        p++;
      t->s.p = pp;
      t->s.len = p - pp;
      t->linep = ps->linep;
      t->line = ps->line;
      t->kind = ID;
      kw(t);
      goto defer;
    }
    goto err;
  }
defer:
  ps->curp = p;
  return;
err:
  rho_panic(ps->ctx, "error: unexpected character '%c' at line %d", *(p - 1),
            ps->line);
}

static void emit(rho_parser *ps, byte c) {
  rho_var *vp;
  byte **pp;
  int n, i;

  pp = &ps->p->code;
  n = ++ps->n;
  *pp = rho_appendgc(ps->ctx, *pp, &c, 1, 1);
  if (!debug)
    return;
  if (n % 2) {
    ps->op = c;
    printf("0x%02X  %s\n", c, OP[c]);
  } else {
    printf("0x%02X  ", c);
    switch (ps->op) {
    case BOP:
      printf("%s", TK[c]);
      break;
    case RET:
      printf("%d", (int)c);
      break;
    case PSHC:
      rho_printv(ps->ctx, ps->p->consts + c, 0);
      break;
    case PSH:
      printf("%-4d (", (int)c);
      vp = ps->p->vars + c;
      for (i = 0; i < vp->name.len; i++)
        putc(vp->name.p[i], stdout);
      printf(")");
      break;
    }
    putc('\n', stdout);
  }
}

rho_closure *rho_load(rho_context *ctx, const char *path) {
  struct stat sb;
  byte *p;
  int fd, n;

  fd = open(path, O_RDONLY);
  if (fd < 0)
    rho_panic(ctx, "rho_load: open failed with errno %d", errno);

  n = fstat(fd, &sb);
  if (n < 0)
    rho_panic(ctx, "rho_load: fstat failed with errno %d", errno);

  p = mmap(0, sb.st_size, PROT_READ, MAP_PRIVATE, fd, 0);
  if (p < 0)
    rho_panic(ctx, "rho_load: mmap failed with errno %d", errno);

  return rho_parse(ctx, (const char *)p);
}

rho_closure *rho_parse(rho_context *ctx, const char *src) {
  rho_closure *cls;
  rho_proto *p;
  rho_parser ps;

  p = rho_alloc(ctx, rho_proto);
  memset(p, 0, sizeof *p);
  cls = makeclosure(ctx, p, 0, 0);

  ps.ctx = ctx;
  ps.src = (byte *)src;
  ps.curp = ps.src;
  ps.linep = ps.src;
  ps.line = 1;
  ps.n = 0;
  ps.p = p;
  ps.ahead.kind = -1;

  next(&ps);
  stmtlist(&ps);
  return cls;
}

bool rho_eq(rho_context *ctx, rho_value *a, rho_value *b) {
  switch (a->tag) {
  case RHO_INT:
    return a->u.i == b->u.i;
  case RHO_FLOAT:
    return a->u.f == b->u.f;
  case RHO_CSTR:
    return strcmp((const char *)a->u.ptr, (const char *)a->u.ptr) == 0;
  default:
    return a->u.ptr == b->u.ptr;
  }
}

int rho_printv(rho_context *ctx, rho_value *vp, char end) {
  int n;

  switch (tag(vp)) {
  case RHO_INT:
    n = printf("%ld", toint(vp));
    break;
  case RHO_FLOAT:
    n = printf("%lf", tofloat(vp));
    break;
  default:
    n = printf("<object 0x%p>", toptr(vp));
    break;
  }
  if (end) {
    putc(end, stdout);
    n++;
  }
  return n;
}

noreturn void rho_panic(rho_context *ctx, const char *fmt, ...) {
  va_list ap;

  traceback(ctx);
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  va_end(ap);
  putc('\n', stderr);
  exit(1);
}

static void traceback(rho_context *ctx) { /* TODO */
}

void *rho_allocgc(rho_context *ctx, int size) {
  rho_runtime *r;
  rho_header *h;
  unsigned bits;

  r = ctx->r;
  if (size > (1 << PMAX)) {
    if (!(h = r->alloc(0, size + sizeof(*h))))
      rho_panic(ctx, "runtime error: out of memory");
    memset(h, 0, sizeof(*h));
    h->size = size;
    h->avail = h->size;
    h->ptr = (void *)(h + 1);
    return h->ptr;
  }
  rho_lock(ctx);
  bits = bits32(size);
  h = r->free[bits];
  if (!h) {
    size = 1 << bits;
    if (!(h = r->alloc(0, size + sizeof(*h))))
      rho_panic(ctx, "runtime error: out of memory");
    memset(h, 0, sizeof(*h));
    h->size = size;
    h->avail = h->size;
    h->ptr = (void *)(h + 1);
    rho_unlock(ctx);
    return h->ptr;
  }
  h->refs = 0;
  h->avail = h->size;
  r->free[bits] = h->next;
  rho_unlock(ctx);
  return h->ptr;
}

void rho_freegc(rho_context *ctx, void *ptr) {
  rho_runtime *r;
  rho_header *h;
  unsigned bits;

  r = ctx->r;
  h = header(ptr);
  if (h->size > (1 << PMAX)) {
    r->alloc(h, 0);
    return;
  }
  bits = bits32(h->size);
  rho_lock(ctx);
  h->next = r->free[bits];
  r->free[bits] = h;
  rho_unlock(ctx);
}

void *rho_reallocgc(rho_context *ctx, void *ptr, int newsz) {
  rho_runtime *r;
  rho_header *h, *newh;

  r = ctx->r;
  h = header(ptr);
  if (newsz > (1 << PMAX)) {
    if (!(h = r->alloc(h, newsz + sizeof(*h))))
      rho_panic(ctx, "runtime error: out of memory");
    h->size = newsz;
    h->avail += newsz - h->size;
    h->ptr = (void *)(h + 1);
    return h->ptr;
  }
  newh = header(rho_allocgc(ctx, newsz));
  memcpy(newh->ptr, h->ptr, h->size);
  newh->avail -= h->size;
  rho_freegc(ctx, h->ptr);
  return newh->ptr;
}

void *rho_appendgc(rho_context *ctx, void *dst, void *src, int n, int usz) {
  rho_header *h;
  int newsz, ncopy;

  ncopy = n * usz;
  if (!dst)
    dst = rho_allocgc(ctx, ncopy);
  h = header(dst);
  if (h->avail < ncopy) {
    newsz = max2(h->size * 3 / 2, h->size + ncopy);
    dst = rho_reallocgc(ctx, dst, newsz);
  }
  /* we have to re-retrieve the header in case of a reallocgc. */
  h = header(dst);
  memcpy(dst + (h->size - h->avail), src, ncopy);
  h->avail -= ncopy;
  return dst;
}

static void *__alloc(void *ptr, int size) {
  if (size != 0)
    return realloc(ptr, size);
  else {
    free(ptr);
    return NULL;
  }
}

rho_value rho_cast(rho_context *ctx, rho_value *vp, int t) {
  switch (t) {
  case RHO_INT:
    switch (tag(vp)) {
    case RHO_INT:
      return *vp;
    case RHO_FLOAT:
      return rho_int(tofloat(vp));
    default:
      return rho_int((long)vp->u.ptr);
    }
    break;
  case RHO_FLOAT:
    switch (tag(vp)) {
    case RHO_FLOAT:
      return *vp;
    case RHO_INT:
      return rho_float(toint(vp));
    default:
      rho_panic(ctx, "runtime error: cannot cast to float");
    }
    break;
  default:
    rho_panic(ctx, "runtime error: cannot cast to %s", TG[t]);
  }
}

rho_runtime *rho_default(void) { return rho_new(__alloc); }

int rho_strcmp(rho_string *s, rho_string *t) {
  int n;
  /* TODO: compare hashes before using strncmp */
  n = s->len - t->len;
  return n == 0 ? strncmp((const char *)s->p, (const char *)t->p, t->len) : n;
}

// int main(int argc, char **argv) {
//   rho_parser ps;
//   rho_runtime *R;
//   rho_context *c0;
//   rho_value v;
//   // int n, i;
//   // Tk tk;
//   // char buf[32];

//   R = rho_new(__alloc);
//   c0 = rho_open(R, 4096);

//   rho_proto p;
//   memset(&p, 0, sizeof p);
//   ps.ctx = c0;
//   ps.p = &p;
//   ps.line = 0;
//   ps.src = (byte *)argv[1];
//   // ps.src = (byte *)"3.0/2";
//   ps.curp = ps.src;
//   ps.ctx = c0;
//   ps.n = 0;

//   next(&ps);
//   expr(&ps, 0);

//   emit(&ps, RET);
//   emit(&ps, 1);

//   // if (!ps.debug) {
//   //   for (i = 0; i < ps.n; i++) {
//   //     printf("0x%02X\n", p.code[i]);
//   //   }
//   // }
//   rho_pushclosure(c0, makeclosure(c0, &p, 0, 0));
//   rho_call(c0, 0);
//   v = rho_pop(c0);
//   rho_printv(c0, &v);
//   exit(0);
//   // printf("%d %d\n", (int)ps.p->code[0], (int)ps.p->code[1]);
//   // printf("%ld\n", ps.p->consts[0].u.i);

//   // for (;;) {
//   //   next(&ps);
//   //   tk = ps.t.kind;
//   //   switch (tk) {
//   //   case EOT:
//   //     exit(0);
//   //   case INT:
//   //   case FLT:
//   //   case ID:
//   //   case STR:
//   //     printf("%s  (", TK[tk]);
//   //     memccpy(buf, ps.t.p, 1, ps.t.len);
//   //     buf[ps.t.len] = '\0';
//   //     printf("%s", buf);
//   //     printf(")\n");
//   //     break;
//   //   default:
//   //     printf("%s\n", TK[tk]);
//   //   }
//   // }
// }
