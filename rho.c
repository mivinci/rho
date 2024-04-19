#include <ctype.h>
#include <errno.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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
};

static char *OP[] = {"nop", "pshc", "pshr", "psh", "pop",
                     "bop", "call", "ret",  "make"};

enum Tk {
  EOT, /* end of token */

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
  CUT, /* // */

  AND, /* & */
  OR,  /* | */
  XOR, /* ^ */

  LAND, /* && */
  LOR,  /* || */

  SHL, /* << */
  SHR, /* >> */

  PARL, /* ( */
  PARR, /* ) */
  COL,  /* : */
  SEM,  /* ; */
  DOT,  /* . */
  COM,  /* , */
};

static char *TK[] = {
    "EOT", "INT", "FLT", "STR", "ID", "++", "--", "~", "!", "+",
    "-",   "*",   "/",   "%",   "**", "//", "&",  "|", "^", "&&",
    "||",  "<<",  ">>",  "(",   ")",  ":",  ";",  ".", ",",
};

static char *TG[] = {"int",   "float",   "pointer", "c string",
                     "proto", "c proto", "closure"};

static int precedence(int tk) {
  switch (tk) {
  case ADD:
  case SUB:
    return 11;
  case MUL:
  case DIV:
  case MOD:
  case POW:
  case CUT:
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
  struct list_head link;
};

struct rho_header {
  rho_header *next;
  int refs;
  int size;
  int avail;
  void *ptr;
};

struct rho_ref {
  rho_ref *next;
  rho_value *vp;
  rho_value v;
};

struct rho_var {
  int islocal : 1;
  int isconst : 1;
  /* Index into proto::vars if var::islocal or closure::refs
     of the enclosing closure. */
  int idx;
};

struct rho_proto {
  rho_proto *prev;
  rho_proto **p;
  rho_var *vars; /* arguments and local variables */
  rho_var *refs;
  rho_value *consts;
  byte *code;
  int nin;
  int nout;
};

struct rho_closure {
  rho_proto *p;
  rho_ref **refs;
};

struct token {
  int kind;
  int len;
  byte *p;
};

struct rho_parser {
  rho_context *ctx;
  rho_proto *p;
  struct token t;
  byte *src;
  byte *curp;
  int line;
  /* Members below are for debug only. */
  int n;
  byte op;
};

static int precedence(int);
static void next(rho_parser *);
static void number(rho_parser *);
static void ident(rho_parser *);
static void stmt(rho_parser *);
static void stmtlist(rho_parser *);
static void unexpr(rho_parser *);
static void expr(rho_parser *, int);
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

rho_context *rho_open(rho_runtime *r, int size) {
  rho_context *ctx;

  rho_assert(r);
  if (!(ctx = r->alloc(0, size * sizeof(rho_value) + sizeof(*ctx))))
    return NULL;
  ctx->sp = (rho_value *)(ctx + 1);
  ctx->top = ctx->sp + size;
  ctx->openrefs = NULL;
  ctx->r = r;
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

static void stmtlist(rho_parser *ps) {
  Tk tk;

  while ((tk = ps->t.kind) != EOT)
    stmt(ps);
  emit(ps, RET);
  emit(ps, 1);
}

static void stmt(rho_parser *ps) {
  expr(ps, 0);
  /* TODO */
}

/* Top-down expression parser. */
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
    tk = ps->t.kind;
    if (tk == INC || tk == DEC) {
      emit(ps, tk);
      next(ps);
    }
    return;
  case ID:
    ident(ps);
    tk = ps->t.kind;
    if (tk == INC || tk == DEC) {
      emit(ps, tk);
      next(ps);
    }
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
    return;
  }
}

static void number(rho_parser *ps) {
  rho_value v, *vp, **vpp;
  int n, i;
  long k;
  double d;

  switch (ps->t.kind) {
  case INT:
    k = strtol((const char *)ps->t.p, NULL, 10);
    if (errno != 0)
      rho_panic(ps->ctx, "parse: strtol failed with errno %d", errno);
    v = rho_int(k);
    break;
  case FLT:
    d = strtod((const char *)ps->t.p, NULL);
    if (errno != 0)
      rho_panic(ps->ctx, "parse: strtod failed with errno %d", errno);
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

static void ident(rho_parser *ps) { /* TODO */
}

#define choose(ps, p, c, t1, t2)                                               \
  do {                                                                         \
    if (*(p) != c)                                                             \
      (ps)->t.kind = t2;                                                       \
    else {                                                                     \
      (ps)->t.kind = t1;                                                       \
      (p)++;                                                                   \
    }                                                                          \
  } while (0)

static void next(rho_parser *ps) {
  byte *p, *pp;
  Tk tk;

  p = ps->curp;

top:
  switch (*p++) {
  case '\0':
    ps->t.kind = EOT;
    goto defer;
  case '\n':
    ps->line++;
    goto top;
  case ' ':
  case '\t':
  case '\r':
    goto top;
  case '/':
    choose(ps, p, '/', CUT, DIV);
    goto defer;
  case '*':
    choose(ps, p, '*', POW, MUL);
    goto defer;
  case '-':
    choose(ps, p, '-', DEC, SUB);
    goto defer;
  case '+':
    choose(ps, p, '+', INC, ADD);
    goto defer;
  case '%':
    ps->t.kind = MOD;
    goto defer;
  case '&':
    choose(ps, p, '&', LAND, AND);
    goto defer;
  case '|':
    choose(ps, p, '|', LOR, OR);
    goto defer;
  case '<':
    if (*p != '<')
      goto err;
    p++;
    ps->t.kind = SHL;
    goto defer;
  case '>':
    if (*p != '>')
      goto err;
    p++;
    ps->t.kind = SHR;
    goto defer;
  case '^':
    ps->t.kind = XOR;
    goto defer;
  case '~':
    ps->t.kind = REV;
    goto defer;
  case '!':
    ps->t.kind = NOT;
    goto defer;
  case '(':
    ps->t.kind = PARL;
    goto defer;
  case ')':
    ps->t.kind = PARR;
    goto defer;
  case ':':
    ps->t.kind = COL;
    goto defer;
  case ';':
    ps->t.kind = SEM;
    goto defer;
  case '.':
    ps->t.kind = DOT;
    goto defer;
  case '"':
    pp = p;
    while (*p != '"' && *p != '\0')
      p++;
    ps->t.p = pp;
    ps->t.len = p - pp;
    ps->t.kind = STR;
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
      ps->t.p = pp;
      ps->t.len = p - pp;
      ps->t.kind = tk;
      goto defer;
    }
    if (isalpha(*(p - 1)) || *(p - 1) == '_') {
      pp = p - 1;
      while (isalpha(*p) || *p == '_')
        p++;
      ps->t.p = pp;
      ps->t.len = p - pp;
      ps->t.kind = ID;
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
  byte **pp;
  int n;

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
    }
    putc('\n', stdout);
  }
}

int rho_load(rho_context *ctx, const char *path) {
  /* TODO */
  return 0;
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
  ps.line = 0;
  ps.n = 0;
  ps.p = p;

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
