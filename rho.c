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
#define len(p)     rho_len(p)
#define cap(p)     rho_cap(p)

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

#define binop_cmp(ctx, op, sp)                                                 \
  do {                                                                         \
    rho_value *p = (sp)--;                                                     \
    switch (tag(sp)) {                                                         \
    case RHO_INT:                                                              \
      toint(sp) = toint(sp) op rho_toint(rho_cast(ctx, p, RHO_INT));           \
      break;                                                                   \
    case RHO_FLOAT:                                                            \
      tofloat(sp) = tofloat(sp) op rho_tofloat(rho_cast(ctx, p, RHO_FLOAT));   \
      break;                                                                   \
    default:                                                                   \
      rho_panic(ctx, "runtime error: invalid operand(s)");                     \
    }                                                                          \
  } while (0)

#define binop_bit(ctx, op, sp)                                                 \
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

typedef rho_byte byte;
typedef enum Op Op;
typedef enum Tk Tk;

enum Op {
  NOP,
  PSHC,
  PSHR,
  PSH,
  POPR,
  POP,
  BOP,
  UOP,
  CALL,
  RET,
  J,
  JB,
  JZ,
  MAKE,
  ATTR,
};

static char *OP[] = {"nop", "pshc", "pshr", "psh",  "popr",
                     "pop", "bop",  "uop",  "call", "ret",
                     "j",   "jb",   "jz",   "make", "attr"};

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
  AT,  /* @ */

  _bop,
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
  LSS, /* < */
  LEQ, /* <= */
  GRT, /* > */
  GEQ, /* >= */
  _bopend,

  ASS, /* = */

  PARL, /* ( */
  PARR, /* ) */
  BRKL, /* [ */
  BRKR, /* ] */
  BRCL, /* { */
  BRCR, /* } */
  COL,  /* : */
  SEM,  /* ; */
  DOT,  /* . */
  COM,  /* , */

  _kw,
  IF,   /* if */
  ELSE, /* else*/
  FOR,  /* for */
  BRK,  /* break */
  CTN,  /* continue */
  VAR,  /* var */
  FN,   /* fn */
  STRT, /* struct */
  _kwend,
};

static char *TK[] = {
    "EOT",      "//",  "INT", "FLT",    "STR",   "ID",   "++",  "--",
    "~",        "!",   "@",   "_bop",   "+",     "-",    "*",   "/",
    "%",        "**",  "&",   "|",      "^",     "&&",   "||",  "<<",
    ">>",       "==",  "!=",  "<",      "<=",    ">",    ">=",  "_bopend",
    "=",        "(",   ")",   "[",      "]",     "{",    "}",   ":",
    ";",        ".",   ",",   "_kw",    "if",    "else", "for", "break",
    "continue", "var", "fn",  "struct", "_kwend"};

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
  case LSS:
  case LEQ:
  case GRT:
  case GEQ:
    return 9;
  case EQ:
  case NEQ:
    return 8;
  case ASS:
    return 1;
  default:
    return 0;
  }
}

struct rho_header {
  rho_header *next;
  int refs;
  int esize;
  int size;
  int avail;
  void *ptr;
};

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

struct rho_ref {
  rho_ref *next;
  rho_value *vp;
  rho_value v;
};

struct rho_var {
  rho_type *type;
  rho_string name;
  int isconst : 1;
  int ispub : 1;
  int scope;
  int idx; /* index into proto::vars of the parent function if ::islocal,
              otherwise index into closure::refs of the parent function.  */
};

struct rho_type {
  rho_string name;
  rho_var *attrs;
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
};

static int precedence(int);
static void next(rho_parser *);
static void peek(rho_parser *);
static void number(rho_parser *);
static void literal(rho_parser *);
static int ident(rho_parser *);
static void block(rho_parser *);
static void stmt(rho_parser *);
static void stmtlist(rho_parser *, Tk);
static void structdecl(rho_parser *);
static void vardecl(rho_parser *);
static void assign(rho_parser *);
static rho_type *arglist(rho_parser *, bool);
static void uexpr(rho_parser *);
static void expr(rho_parser *, int);
static void exprlist(rho_parser *);
static void ifexpr(rho_parser *);
static void forexpr(rho_parser *);
static void scan(rho_parser *, struct token *);
static void emit(rho_parser *, byte);
static void traceback(rho_context *);
static rho_var *findvar(rho_parser *, struct token *);
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
  int usz, sz;

  usz = sizeof(struct rho_type);
  sz = 3 * usz;
  tp = rho_callocgc(ctx, 3, usz);
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
      break;
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
        binop_bit(ctx, %, sp);
        break;
      case AND:
        binop_bit(ctx, &, sp);
        break;
      case OR:
        binop_bit(ctx, |, sp);
        break;
      case XOR:
        binop_bit(ctx, ^, sp);
        break;
      case SHL:
        binop_bit(ctx, <<, sp);
        break;
      case SHR:
        binop_bit(ctx, >>, sp);
        break;
      case EQ:
        binop_cmp(ctx, >=, sp);
        break;
      case NEQ:
        binop_cmp(ctx, >=, sp);
        break;
      case LSS:
        binop_cmp(ctx, <, sp);
        break;
      case LEQ:
        binop_cmp(ctx, <=, sp);
        break;
      case GRT:
        binop_cmp(ctx, >, sp);
        break;
      case GEQ:
        binop_cmp(ctx, >=, sp);
        break;
      }
      break;
    case UOP:
      a = *pc++;
      switch (a) {
      case NOT:
        sp->u.i = !sp->u.i;
        break;
      case REV:
        sp->u.i = ~sp->u.i;
        break;
      case INC:
        sp->u.i++;
        break;
      case DEC:
        sp->u.i--;
        break;
      case AT:
        rho_println(ctx, sp);
        break;
      }
      break;
    case J: /* Jump to pc+a */
      a = *pc++;
      pc += a;
      break;
    case JB: /* Jump to pc-a */
      a = *pc++;
      pc -= a;
      break;
    case JZ: /* Jump to pc+a if TOS is falsy */
      a = *pc++;
      if (!(sp->u.i))
        pc += a;
      sp--; /* drop the value used for comparison */
      break;
    case NOP:
      break;
    default:
      rho_panic(ctx, "runtime error: bad opcode %s", OP[*(pc - 1)]);
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
    if (ref->scope <= 1)
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

noreturn static void syntaxerror(rho_parser *ps, const char *fmt, ...) {
  va_list ap;
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
  for (i = 0; i < t->s.len - 1; i++)
    *bp++ = '~';
  *bp++ = '\n';
  for (i = 0; i < n; i++)
    *bp++ = ' ';
  *bp++ = '|';
  *bp++ = '\n';
  *bp++ = '\0';
  fprintf(stderr, b);
  fprintf(stderr, "syntax error: ");
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  va_end(ap);
  putc('\n', stderr);
  exit(1);
}

#define expect(ps, tk)                                                         \
  do {                                                                         \
    if (ps->t.kind != tk)                                                      \
      syntaxerror(ps, "expect token '%s'", TK[tk]);                            \
  } while (0)

static void stmtlist(rho_parser *ps, Tk end) {
  Tk tk;

  tk = ps->t.kind;
  while (tk != end && tk != EOT) {
    stmt(ps);
    tk = ps->t.kind;
  }
}

static void stmt(rho_parser *ps) {
  Tk tk, ah;

  tk = ps->t.kind;
  switch (tk) {
  case BRK:
    emit(ps, J);
    emit(ps, NOP);
    /* TODO: save */
    next(ps);
    return;
  case CMT:
    next(ps);
    return;
  case VAR:
    vardecl(ps);
    return;
  case FN:
    /* TODO: function declaration*/
    return;
  case STRT:
    structdecl(ps);
    return;
  case ID:
    /* TODO:  */
    peek(ps);
    ah = ps->ahead.kind;
    if (ah == ASS || ah == COM) {
      assign(ps);
      return;
    }
    /* otherwise fall back to expr */
  default:
    expr(ps, 0); /* expression */
  }
}

static void block(rho_parser *ps) {
  expect(ps, BRCL);
  next(ps);
  stmtlist(ps, BRCR);
  expect(ps, BRCR);
  next(ps);
}

/*
ifexpr := 'if' expr block [ 'else' block ]

s0            s0
if s1 {       s1
  s2          jz -> s3
} else {      s2
  s3          j  -> s4
}             s3
s4            s4
*/
static void ifexpr(rho_parser *ps) {
  byte **pp;
  int n, s2, s3;

  pp = &ps->p->code;
  expect(ps, IF);
  next(ps);
  expr(ps, 0); /* s1 */
  emit(ps, JZ);
  emit(ps, NOP);
  s2 = len(*pp);
  block(ps); /* s2 */
  if (ps->t.kind == ELSE) {
    emit(ps, J);
    emit(ps, NOP);
    next(ps);
    s3 = len(*pp);
    block(ps); /* s3 */
    n = len(*pp);
    (*pp)[s3 - 1] = n - s3;
  }
  (*pp)[s2 - 1] = s3 - s2;
}

/*
forexpr := 'for' [ stmt ] ';' [ expr ] ';' [ stmt ] block

s0                   s0
for s1; s2; s3 {     s1
  s4                 s2
}                    jz -> s5
s5                   j  -> s4
                     s3
                     j  -> s2
                     s4
                     j  -> s3
                     s5
*/
static void forexpr(rho_parser *ps) {
  byte **pp;
  int j5, j4, j2, j3, s2, s3;

  pp = &ps->p->code;
  expect(ps, FOR);
  next(ps);
  if (ps->t.kind != SEM)
    stmt(ps); /* s1 */
  expect(ps, SEM);
  next(ps);
  s2 = len(*pp);
  if (ps->t.kind != SEM)
    expr(ps, 0); /* s2 */
  emit(ps, JZ);
  emit(ps, NOP);
  j5 = len(*pp);
  emit(ps, J);
  emit(ps, NOP);
  j4 = len(*pp);
  expect(ps, SEM);
  next(ps);
  s3 = len(*pp);
  if (ps->t.kind != BRCL)
    stmt(ps); /* s3 */
  emit(ps, JB);
  emit(ps, NOP);
  j2 = len(*pp);
  block(ps); /* s4 */
  emit(ps, JB);
  emit(ps, NOP);
  j3 = len(*pp);

  (*pp)[j5 - 1] = j3 - j5;
  (*pp)[j4 - 1] = j2 - s3;
  (*pp)[j2 - 1] = j2 - s2;
  (*pp)[j3 - 1] = j3 - s3;
}

/* vardecl := 'var' arglist */
static void vardecl(rho_parser *ps) {
  expect(ps, VAR);
  next(ps);
  arglist(ps, false);
  next(ps);
}

/* arglist := ID [ ',' ID ] type */
static rho_type *arglist(rho_parser *ps, bool isconst) {
  rho_var v, *vp, **vpp;
  rho_type *tp;
  int n, k, i;

  expect(ps, ID);
  n = len(ps->p->vars);
  for (k = 0; k < n; k++) {
    vp = ps->p->vars + k;
    if (rho_strcmp(&vp->name, &ps->t.s) == 0)
      syntaxerror(ps, "redundant variable declaration");
  }
  v.idx = k;
  v.isconst = isconst;
  v.name = ps->t.s;
  v.scope = 0;
  vpp = &ps->p->vars;
  *vpp = rho_append(ps->ctx, *vpp, &v, 1, rho_var);

  next(ps);
  switch (ps->t.kind) {
  case ID:
    n = len(ps->ctx->types);
    for (i = 0; i < n; i++) {
      tp = ps->ctx->types + i;
      if (rho_strcmp(&tp->name, &ps->t.s) == 0) {
        (*vpp)[k].type = tp;
        return tp;
      }
    }
    syntaxerror(ps, "undefined type");
  case COM:
    next(ps);
    tp = arglist(ps, isconst);
    if (tp)
      (*vpp)[k].type = tp;
    return tp;
  default:
    syntaxerror(ps, "unexpected token");
  }
}

static rho_type *findtype(rho_parser *ps, struct token *t) {
  rho_type *tp;
  int n, i;

  n = len(ps->ctx->types);
  for (i = 0; i < n; i++) {
    tp = ps->ctx->types + i;
    if (rho_strcmp(&tp->name, &t->s) == 0)
      return tp;
  }
  return NULL;
}

static void structdecl(rho_parser *ps) {
  rho_type t, *tp, **tpp, *ap;
  rho_var v;
  int i;

  expect(ps, STRT);
  next(ps);

  tp = findtype(ps, &ps->t);
  if (tp)
    syntaxerror(ps, "redundant type definition");

  t.name = ps->t.s;
  t.attrs = NULL;
  /* we must append t before moving to its attributes who's
     type can also be t  */
  tpp = &ps->ctx->types;
  *tpp = rho_append(ps->ctx, *tpp, &t, 1, rho_type);
  tp = *tpp + len(*tpp) - 1;

  next(ps);
  expect(ps, BRCL);
  next(ps);

  i = 0;
  while (ps->t.kind != BRCR) {
    expect(ps, ID);
    v.name = ps->t.s;
    next(ps);
    expect(ps, ID);
    ap = findtype(ps, &ps->t);
    if (!ap)
      syntaxerror(ps, "undefined type");
    v.type = ap;
    v.idx = i;
    tp->attrs = rho_append(ps->ctx, tp->attrs, &v, 1, rho_var);
    next(ps);
    i++;
  }
  next(ps);
}

/* assign := ID [ ',' ID ]+ [ bop ] '=' exprlist */
static void assign(rho_parser *ps) {
  rho_var *vp;

  expect(ps, ID);
  vp = findvar(ps, &ps->t);

  next(ps);
  switch (ps->t.kind) {
  case ASS:
    next(ps);
    exprlist(ps);
    goto end;
  case COM:
    next(ps);
    assign(ps);
    goto end;
  default:
    syntaxerror(ps, "unexpected token");
  }
end:
  /* TODO: statistic analysis for types */
  emit(ps, vp->scope == 0 ? POP : POPR);
  emit(ps, vp->idx);
}

static void exprlist(rho_parser *ps) {
  expr(ps, 0);
  while (ps->t.kind == COM) {
    next(ps);
    expr(ps, 0);
  }
}

/* Top-down expression parsing. */
static void expr(rho_parser *ps, int plv) {
  Tk tk;
  int lv;

  tk = ps->t.kind;
  if (tk == EOT)
    return;

  uexpr(ps); /* left branch */
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

static void uexpr(rho_parser *ps) {
  Tk tk;
  int n;

  tk = ps->t.kind;
  switch (tk) {
  case INT:
  case FLT:
    number(ps);
    return;
  case STR:
    literal(ps);
    return;
  case ID:
    /* TODO */
    n = ident(ps);
    tk = ps->t.kind;
    if (tk == INC || tk == DEC) {
      emit(ps, UOP);
      emit(ps, tk);
      emit(ps, POP);
      emit(ps, n);
      next(ps);
    }
    return;
  case NOT:
  case REV:
  case AT:
    next(ps);
    expr(ps, 0);
    emit(ps, UOP);
    emit(ps, tk);
    return;
  case IF:
    ifexpr(ps);
    return;
  case FOR:
    forexpr(ps);
    return;
  case PARL:
    next(ps);
    expr(ps, 0);
    tk = ps->t.kind;
    if (tk != PARR)
      syntaxerror(ps, "open parentheses");
    next(ps);
    return;
  default:
    syntaxerror(ps, "unexpected token");
  }
}

static void constant(rho_parser *ps, rho_value *vp) {
  rho_value *p, **vpp;
  int n, i;

  n = len(ps->p->consts);
  for (i = 0; i < n; i++) {
    p = ps->p->consts + i;
    if (rho_eq(ps->ctx, p, vp))
      goto end;
  }
  vpp = &ps->p->consts;
  if (i == n)
    *vpp = rho_append(ps->ctx, *vpp, vp, 1, rho_value);
end:
  emit(ps, PSHC);
  emit(ps, i);
}

static void literal(rho_parser *ps) {
  rho_value v;

  v.tag = STR;
  v.u.s = ps->t.s;
  constant(ps, &v);
  next(ps);
}

static void number(rho_parser *ps) {
  rho_value v;
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
  constant(ps, &v);
  next(ps);
}

static rho_var *findvar(rho_parser *ps, struct token *t) {
  rho_var v, *vp, **vpp;
  rho_proto *p;
  int n, i, scope;

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
  syntaxerror(ps, "undefined variable");

end:
  v = *vp;
  v.scope = scope;
  if (scope > 0) {
    *vpp = rho_append(ps->ctx, *vpp, &v, 1, rho_var);
    vp = (*vpp) + (len(*vpp) - 1);
  }
  return vp;
}

static int ident(rho_parser *ps) {
  rho_var *vp;

  vp = findvar(ps, &ps->t);
  emit(ps, vp->scope == 0 ? PSH : PSHR);
  emit(ps, vp->idx);
  next(ps);
  return vp->idx;
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

static void kw(struct token *t) {
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
    switch (*p) {
    case '<':
      t->kind = SHL;
      break;
    case '=':
      t->kind = LEQ;
      break;
    default:
      t->kind = LSS;
    }
    p++;
    t->linep = ps->linep;
    t->line = ps->line;
    goto defer;
  case '>':
    switch (*p) {
    case '>':
      t->kind = SHR;
      break;
    case '=':
      t->kind = GEQ;
      break;
    default:
      t->kind = GRT;
    }
    p++;
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
  case '{':
    t->kind = BRCL;
    t->linep = ps->linep;
    t->line = ps->line;
    goto defer;
  case '}':
    t->kind = BRCR;
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
  case '@':
    t->kind = AT;
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
  rho_panic(ps->ctx, "scan error: unexpected character '%c' at line %d",
            *(p - 1), ps->line);
}

static void emit(rho_parser *ps, byte c) {
  byte **pp;

  pp = &ps->p->code;
  *pp = rho_append(ps->ctx, *pp, &c, 1, byte);
}

int rho_dump(rho_context *ctx, rho_closure *cls, FILE *fp) {
  rho_var *vp;
  byte op, a, *p;
  int n, i, k, l;

  p = cls->p->code;
  n = len(p);
  for (k = 0; k < n; k += 2) {
    l = k + 1;
    op = p[k];
    a = p[l];
    fprintf(fp, "%4d    0x%02X    %s\n", k, op, OP[op]);
    fprintf(fp, "%4d    0x%02X    ", l, a);
    switch (op) {
    case UOP:
    case BOP:
      fprintf(fp, "%-5d (%s)", a, TK[a]);
      break;
    case RET:
      fprintf(fp, "%d", a);
      break;
    case PSHC:
      fprintf(fp, "%-5d (", a);
      rho_printv(ctx, cls->p->consts + a, 0, true);
      fprintf(fp, ")");
      break;
    case PSHR:
    case POPR:
      fprintf(fp, "%-5d (", a);
      vp = cls->p->refs + a;
      for (i = 0; i < vp->name.len; i++)
        putc(vp->name.p[i], fp);
      fprintf(fp, ")");
      break;
    case PSH:
    case POP:
      fprintf(fp, "%-5d (", a);
      vp = cls->p->vars + a;
      for (i = 0; i < vp->name.len; i++)
        putc(vp->name.p[i], fp);
      fprintf(fp, ")");
      break;
    case J:
    case JB:
    case JZ:
      fprintf(fp, "%-5d (", a);
      fprintf(fp, "%d)", 1 + l + (op == JB ? -a : a));
      break;
    }
    putc('\n', fp);
  }
  return 0;
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
  ps.p = p;
  ps.ahead.kind = -1;

  next(&ps);
  stmtlist(&ps, EOF);
  emit(&ps, RET);
  emit(&ps, 1);
  return cls;
}

bool rho_eq(rho_context *ctx, rho_value *a, rho_value *b) {
  switch (a->tag) {
  case RHO_INT:
    return a->u.i == b->u.i;
  case RHO_FLOAT:
    return a->u.f == b->u.f;
  case RHO_STR:
    return strcmp((const char *)a->u.ptr, (const char *)b->u.ptr) == 0;
  default:
    return a->u.ptr == b->u.ptr;
  }
}

int rho_printv(rho_context *ctx, rho_value *vp, char end, bool quote) {
  int n, i;

  switch (tag(vp)) {
  case RHO_INT:
    n = printf("%ld", toint(vp));
    break;
  case RHO_FLOAT:
    n = printf("%lf", tofloat(vp));
    break;
  case RHO_STR:
    if (quote)
      putc('"', stdout);
    for (i = 0; i < vp->u.s.len; i++)
      putc(vp->u.s.p[i], stdout);
    if (quote)
      putc('"', stdout);
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
    h->esize = size;
    h->size = size;
    h->avail = h->size;
    h->ptr = (void *)(h + 1);
    rho_unlock(ctx);
    return h->ptr;
  }
  h->refs = 0;
  h->avail = h->size;
  h->esize = h->size;
  r->free[bits] = h->next;
  rho_unlock(ctx);
  return h->ptr;
}

void *rho_callocgc(rho_context *ctx, int n, int usz) {
  void *p;

  p = rho_allocgc(ctx, n * usz);
  header(p)->esize = usz;
  return p;
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
  newh->esize = h->esize;
  memcpy(newh->ptr, h->ptr, h->size);
  newh->avail -= (h->size - h->avail);
  rho_freegc(ctx, h->ptr);
  return newh->ptr;
}

void *rho_appendgc(rho_context *ctx, void *dst, void *src, int n, int usz) {
  rho_header *h;
  int newsz, ncopy;

  if (!dst)
    dst = rho_callocgc(ctx, n, usz);

  h = header(dst);
  ncopy = n * usz;
  if (h->avail < ncopy) {
    newsz = max2(h->size * 2, h->size + ncopy);
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

int rho_cap(void *p) {
  rho_header *h;

  if (!p)
    return 0;
  h = header(p);
  return h->size / h->esize;
}

int rho_len(void *p) {
  rho_header *h;

  if (!p)
    return 0;
  h = header(p);
  return (h->size - h->avail) / h->esize;
}
