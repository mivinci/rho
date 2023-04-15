/*
fn a(x) {
  fn b(y) {
    fn c(z) {
      x + y + z
    }
  }
}

main: pshc     0 (proto)
      closure
      popv     0 (a)
      ret
a:    pshv     0 (x)
      pshc     1 (proto)
      closure
      popv     1 (b)
      ret
b:    pshv     0 (y)
      pshc     1 (proto)
      closure
      popv     1 (c)
      ret
c:    pshv     0 (z)
      pshr     0 (x)
      pshr     1 (y)
      pshv     0 (z)
      add
      add
      ret


1+2

main: pshc    0 (1)
      pshc    1 (2)
      add
*/

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "list.h"

#define u8 unsigned char
#define u16 unsigned short
#define u32 unsigned int
#define i32 long
#define f32 double
#define usize size_t

#define RHO_PMAX 10

#define nop ((void)0)

#define rho_allocator ((struct allocator){malloc, realloc, free})
#define rho_allocex(c, t, e) ((t *)allocgc(c, sizeof(t) + e))
#define rho_alloc(c, t) rho_allocex(c, t, 0)
#define rho_free(c, p) freegc(c, p)
#define rho_append(c, d, s, n, t) ((t *)append(c, d, s, n, sizeof(t)))

#define rho_lock(c) nop
#define rho_unlock(c) nop

#define rho_panic(c, ...) panic(c, __VA_ARGS__)
#define rho_push(c, v) (*c->top++ = v)
#define rho_pop(c) (*(--c->top))

#define tag(p) ((p)->tag)
#define isnum(p) (tag(p) == RHO_INT || tag(p) == RHO_FLT)

#define rho_any(p, t) ((struct value){.tag = t, .u.ptr = p})
#define rho_closure(p) rho_any(p, RHO_CLOSURE)
#define rho_proto(p) rho_any(p, RHO_PROTO)
#define rho_cproto(p) rho_any(p, RHO_CPROTO)
#define rho_str(p) rho_any(p, RHO_STR)
#define rho_uint(v) ((struct value){.tag = RHO_UINT, .u.u = v})
#define rho_int(v) ((struct value){.tag = RHO_INT, .u.i = v})
#define rho_float(v) ((struct value){.tag = RHO_FLT, .u.r = v})

#define getany(p, t) ((t)(p)->u.ptr)
#define getclosure(p) getany(p, struct closure *)
#define getproto(p) getany(p, struct proto *)
#define getcproto(p) getany(p, cproto)
#define getstr(p) getany(p, const char *)
#define getuint(p) ((p)->u.u)
#define getint(p) ((p)->u.i)
#define getflt(p) ((p)->u.r)
#define getnum(p) (tag(p) == RHO_INT ? getint(p) : getflt(p))

#define header(p) ((struct header *)((char *)(p) - sizeof(struct header)))
#define avail(p) (header(p)->avail)
#define size(p) (header(p)->size)
#define len(p) ((size(p) - avail(p)) / sizeof(*p))
#define cap(p) (size(p) / sizeof(*p))
#define size_expect(p) (1 << bits32(sizeof(*(p))))

#define bits32(x) (32 - __builtin_clz(x))
#define max(a, b) ((a) > (b) ? (a) : (b))

#define vmbinop(op, top)                                                       \
  {                                                                            \
    struct value *s = --top - 1;                                               \
    switch (tag(s)) {                                                          \
    case RHO_INT:                                                              \
      getint(s) op## = getint(top);                                            \
    case RHO_UINT:                                                             \
      getuint(s) op## = getuint(s);                                            \
    default:                                                                   \
      getflt(s) op## = getflt(top);                                            \
    }                                                                          \
  }

#define vmjmpop(op, pc, top)                                                   \
  if (getnum(--top) op 0)                                                      \
    pc += (*(u16 *)pc);

enum token {
  TK_UNKNOWN,
  TK_EOF,
  TK_IDENT,
};

enum opcode {
  OP_rsvd,  // reserved.
  OP_print, // for debuging, will be removed.
  OP_cls,   // pops TOS out to create a closure instance onto the stack.
  OP_call,  // call TOS.
  OP_ret,   // returns to the previous stack frame.
  OP_pshv,  // pushes a variable from var[i] onto the stack.
  OP_pshc,  // pushes a constant from cons[i] onto the stack.
  OP_pshr,  // pushes a reference from ref[i] onto the stack.
  OP_popv,  // pops TOS out to var[i].
  OP_popr,  // pops TOS out to ref[i].
  OP_add,   // pops TOS and adds it to TOS-1.
  OP_sub,   // pops TOS and substracts it from TOS-1.
  OP_cmp,   // pops TOS and TOS-1 and then pushes TOS-(TOS-1) onto the stack.
  OP_jpn,   // moves pc i step forward if TOS < 0
  OP_jpp,   // moves pc i step forward if TOS > 0
  OP_jpz,   // moves pc i step forward if TOS == 0
};

enum tag {
  RHO_UINT,
  RHO_INT,
  RHO_FLT,
  RHO_STR,
  RHO_PROTO,
  RHO_CPROTO,
  RHO_CLOSURE,
};

struct value {
  enum tag tag;
  union {
    u32 u;
    i32 i;
    f32 r;
    void *ptr;
  } u;
};

struct header {
  struct header *next;
  u8 marked : 1;
  u8 color : 2;
  usize rc;    // reference count.
  usize size;  // size allocated for ptr.
  usize avail; // size unused
  void *ptr;
};

struct allocator {
  void *(*alloc)(usize);
  void *(*realloc)(void *, usize);
  void (*free)(void *);
};

struct tokenval {
  u8 len;
  const char *text;
};

struct parser {
  struct context *ctx;
  struct proto *proto;
  enum token token;
  enum token ahead;
  const char *buf;
};

// compile time structs

struct var {
  u8 islocal : 1;
  u8 isconst : 1;
  u16 idx;  // index into proto::vars if islocal, otherwise into
            // closure::refs of the enclosing closure.
  u32 name; // index into runtime::symbols
};

struct proto {
  u32 name;             // index into runtime::symbols.
  usize nrefs;          // number of references.
  usize nargs;          // number of arguments.
  usize nlocs;          // number of local variables.
  struct proto **p;     // child-protos defined in this proto.
  struct value *consts; // constants defined in this proto.
  struct var *refs;     // references appeared in this proto.
  struct var *vars;     // variables (arguments and local variables)
                        // defined in this proto.
  u8 *buf;              // bytecode compiled for this proto.
};

// runtime structs

struct ref {
  struct ref *next;
  struct value *pv;
  struct value v;
};

struct closure {
  struct proto *proto;
  struct ref **refs;
};

struct context {
  struct list_head node;
  struct runtime *rt;
  struct ref *openrefs;
  struct value *base;
  struct value *top;
};

struct runtime {
  struct list_head threads;
  struct allocator allocator;
  struct header *allocated[RHO_PMAX];
};

typedef int (*cproto)(struct context *, int);

static void panic(struct context *ctx, const char *fmt, ...) {
  // TODO: do stack frame traceback via ctx.
  va_list ap;
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  putc('\n', stderr);
  va_end(ap);
  exit(1);
}

struct runtime *rho_new(struct allocator al) {
  struct runtime *rt;
  if (!(rt = al.alloc(sizeof(*rt))))
    return NULL;
  rt->allocator = al;
  list_head_init(&rt->threads);
  return rt;
}

void rho_drop(struct runtime *rt) { rt->allocator.free(rt); }

struct context *rho_open(struct runtime *rt, usize size) {
  struct context *ctx;
  void *ptr;
  if (!(ptr = rt->allocator.alloc(size + sizeof(*ctx))))
    return NULL;
  ctx = (struct context *)ptr;
  ctx->base = (struct value *)(ptr + sizeof(*ctx));
  ctx->top = ctx->base;
  ctx->openrefs = NULL;
  ctx->rt = rt;
  list_add(&ctx->node, &rt->threads);
  return ctx;
}

void rho_close(struct context *ctx) {
  list_del(&ctx->node);
  ctx->rt->allocator.free(ctx);
}

static void *allocgc(struct context *ctx, usize size) {
  struct runtime *rt = ctx->rt;
  struct header *hdr;
  usize bits;
  if (size > (1 << RHO_PMAX)) {
    if (!(hdr = rt->allocator.alloc(size + sizeof(*hdr))))
      rho_panic(ctx, "out of memory");
    memset(hdr, 0, sizeof(*hdr));
    hdr->size = size;
    hdr->avail = hdr->size;
    hdr->ptr = (void *)(hdr + 1);
    return hdr->ptr;
  }
  rho_lock(ctx);
  bits = bits32(size);
  hdr = rt->allocated[bits];
  if (!hdr) {
    size = 1 << bits;
    if (!(hdr = rt->allocator.alloc(size + sizeof(*hdr))))
      rho_panic(ctx, "out of memory");
    memset(hdr, 0, sizeof(*hdr));
    hdr->size = size;
    hdr->avail = hdr->size;
    hdr->ptr = (void *)(hdr + 1);
    rho_unlock(ctx);
    return hdr->ptr;
  }
  hdr->rc = 0;
  hdr->avail = hdr->size;
  rt->allocated[bits] = hdr->next;
  rho_unlock(ctx);
  return hdr->ptr;
}

static void freegc(struct context *ctx, void *ptr) {
  struct runtime *rt = ctx->rt;
  struct header *hdr = header(ptr);
  usize bits;
  if (hdr->size > (1 << RHO_PMAX)) {
    rt->allocator.free(hdr);
    return;
  }
  bits = bits32(hdr->size);
  rho_lock(ctx);
  hdr->next = rt->allocated[bits];
  rt->allocated[bits] = hdr;
  rho_unlock(ctx);
}

static void *reallocgc(struct context *ctx, void *ptr, usize newsize) {
  struct runtime *rt = ctx->rt;
  struct header *hdr = header(ptr), *newhdr;
  if (newsize > (1 << RHO_PMAX)) {
    if (!(hdr = rt->allocator.realloc(hdr, newsize + sizeof(*hdr))))
      rho_panic(ctx, "out of memory");
    hdr->size = newsize;
    hdr->avail += newsize - hdr->size;
    hdr->ptr = (void *)(hdr + 1);
    return hdr->ptr;
  }
  newhdr = allocgc(ctx, newsize);
  memcpy(newhdr->ptr, hdr->ptr, hdr->size);
  freegc(ctx, hdr->ptr);
  return newhdr->ptr;
}

static void *append(struct context *ctx, void *dst, const void *src, usize n,
                    usize usz) {
  struct header *hdr;
  usize newsize, ncopy = n * usz;
  if (!dst)
    dst = allocgc(ctx, ncopy);
  hdr = header(dst);
  if (hdr->avail < ncopy) {
    newsize = max(hdr->size * 3 / 2, hdr->size + ncopy);
    dst = reallocgc(ctx, dst, newsize);
  }
  hdr = header(dst); // we have to re-gain the header in case of a reallocgc.
  memcpy(dst + (hdr->size - hdr->avail), src, ncopy);
  hdr->avail -= ncopy;
  return dst;
}

struct ref *findref(struct context *ctx, struct value *level) {
  struct ref *p, **pp = &ctx->openrefs;
  while ((p = *pp) && p->pv >= level) {
    if (p->pv == level)
      return p;
    pp = &p->next;
  }
  p = rho_alloc(ctx, struct ref);
  p->pv = level;
  p->next = *pp;
  *pp = p;
  return p;
}

struct closure *closure(struct context *ctx, struct proto *proto,
                        struct ref **enc_refs, struct value *base) {
  usize i;
  usize nrefs = proto->nrefs;
  struct closure *cls = rho_allocex(ctx, struct closure, nrefs);
  struct var *ref;
  cls->proto = proto;
  for (i = 0; i < nrefs; i++) {
    ref = proto->refs + i;
    if (ref->islocal)
      cls->refs[i] = findref(ctx, base + ref->idx);
    else
      cls->refs[i] = enc_refs[ref->idx];
  }
  return cls;
}

void closerefs(struct context *ctx, struct value *level) {
  struct ref *p = ctx->openrefs;
  while (p && p->pv >= level) {
    p->v = *p->pv;
    p->pv = &p->v;
    p = p->next;
    ctx->openrefs = p; // remove closed ref from context::openrefs.
  }
}

static void printv(const char *s, struct value *v) {
  switch (tag(v)) {
  case RHO_INT:
    printf("%s%ld\n", s, getint(v));
    break;
  case RHO_FLT:
    printf("%s%f\n", s, getflt(v));
    break;
  case RHO_STR:
    printf("%s%s\n", s, getstr(v));
    break;
  default:
    printf("%s<object 0x%p>\n", s, getany(v, void *));
  }
}

// Given the number of input arguments nargs, call calls TOS and returns the
// number of output arguments, therefore, the base is top - nargs, input
// arguments are [base, top) and the output arguments are [base, n).
int call(struct context *ctx, int nargs) {
  struct value *top, *base, *val;
  struct closure *cls;
  u8 *pc;
  top = ctx->top;
  base = top - nargs;
  val = base - 1;
  if (tag(val) == RHO_CPROTO)
    return getcproto(val)(ctx, nargs);
  if (tag(val) != RHO_CLOSURE)
    rho_panic(ctx, "not callable");
  cls = getclosure(val);
  if (cls->proto->nargs > nargs)
    rho_panic(ctx, "expect more arguments");
  pc = cls->proto->buf;
  while (1) {
    switch (*pc++) {
    case OP_print:
      printv("", top - 1);
      break;
    case OP_cls:
      top[-1] = rho_closure(closure(ctx, getproto(top - 1), cls->refs, base));
      break;
    case OP_call:
      ctx->top = top;
      top = base + call(ctx, *pc++);
      break;
    case OP_ret:
      if (ctx->openrefs)
        closerefs(ctx, base);
      return top - base;
    case OP_pshv:
      *top++ = base[*pc++];
      break;
    case OP_pshc:
      *top++ = cls->proto->consts[*pc++];
      break;
    case OP_pshr:
      *top++ = *cls->refs[*pc++]->pv;
      break;
    case OP_popv:
      base[*pc++] = top[-1];
      break;
    case OP_popr:
      cls->refs[*pc++]->pv = --top;
      break;
    case OP_add:
      vmbinop(+, top);
      break;
    case OP_sub:
      vmbinop(-, top);
      break;
    case OP_cmp:
      if (isnum(top - 1) && isnum(top - 2)) {
        vmbinop(-, top);
        break;
      }
      // TODO: compare string literal
      break;
    case OP_jpn:
      vmjmpop(<, pc, top);
      break;
    case OP_jpp:
      vmjmpop(>, pc, top);
      break;
    case OP_jpz:
      vmjmpop(==, pc, top);
      break;
    }
  }
}

static void scan(struct parser *ps) {}

static int next(struct parser *ps) {
  if (ps->ahead != TK_UNKNOWN) {
    ps->ahead = TK_UNKNOWN;
    return ps->ahead;
  }
  scan(ps);
  return ps->token;
}

int parse(struct parser *ps) { return 0; }

int eval(struct context *ctx, const char *s, usize n) {
  int err;
  struct parser ps;
  struct proto proto;
  ps.proto = &proto;
  ps.ctx = ctx;
  if ((err = parse(&ps)) < 0)
    return err;
  rho_push(ctx, rho_closure(closure(ctx, &proto, NULL, ctx->base)));
  return call(ctx, 0);
}

static inline void emit(struct context *ctx, u8 **p, u8 *buf, usize n) {
  *p = rho_append(ctx, *p, buf, n, u8);
}

static void emit8(struct context *ctx, u8 **p, u8 v) { emit(ctx, p, &v, 1); }
static void emit16(struct context *ctx, u8 **p, u16 v) {
  emit(ctx, p, (u8 *)&v, 2);
}

struct assembler {
  struct context *ctx;
  struct proto *p;
  const char *buf;
  usize lineno;
};

static void asm_syntaxerror(struct assembler *p, const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  fprintf(stderr, "syntax error at line %ld: ", p->lineno);
  vfprintf(stderr, fmt, ap);
  va_end(ap);
  putc('\n', stderr);
}

#define skipspaces(s)                                                          \
  while (*++s == ' ')                                                          \
    ;

#define skipcomment(s)                                                         \
  while (*++s != '\n')                                                         \
    ;

static int asm_parse(struct assembler *a) {
  struct value v;
  struct proto *p = a->p;
  const char *s = a->buf;
  int op;
  while (*s != 0) {
    switch (*s++) {
    case '\n':
    case '\t':
    case ' ':
      if (*s == '\n')
        a->lineno++;
      break;
    case '.':
      if (strncmp(s, "int", 3) == 0) {
        s += 3;
        skipspaces(s);
        v = rho_int(atoi(s));
      } else if (strncmp(s, "flt", 3) == 0) {
        s += 3;
        skipspaces(s);
        v = rho_float(atof(s));
      } else {
        asm_syntaxerror(a, "unexpected token: p%c%c%c", s[-3], s[-2], s[-1]);
        return -1;
      }
      p->consts = rho_append(a->ctx, p->consts, &v, 1, struct value);
      skipcomment(s);
      break;
    case 'p':
      if (strncmp(s, "rint", 4) == 0) {
        s += 4;
        emit8(a->ctx, &p->buf, (u8)OP_print);
        continue;
      }
      if (*s++ == 's' && *s++ == 'h') {
        switch (*s++) {
        case 'c':
          op = OP_pshc;
          break;
        case 'v':
          op = OP_pshv;
          break;
        case 'r':
          op = OP_pshr;
          break;
        }
      } else if (*s++ == 'o' && *s++ == 'p') {
        switch (*s++) {
        case 'v':
          op = OP_popv;
          break;
        case 'r':
          op = OP_popr;
          break;
        }
      } else {
        asm_syntaxerror(a, "unexpected token: p%c%c%c", s[-3], s[-2], s[-1]);
        return -1;
      }
      emit8(a->ctx, &p->buf, (u8)op);
      skipspaces(s);
      emit8(a->ctx, &p->buf, (u8)atoi(s));
      skipcomment(s);
      break;
    }
  }
  return 0;
}

int repl(struct context *ctx) {
  struct closure *cls;
  struct assembler a = {
    .ctx = ctx,
    .lineno = 0,
    .p = rho_alloc(ctx, struct proto),
  };
  int err;
  char buf[32];
  while (1) {
    printf("rho$ ");
    fgets(buf, 32, stdin);
    if (*buf == '\n')
      break;
    a.buf = buf;
    if ((err = asm_parse(&a)) < 0)
      return err;
  }
  cls = closure(ctx, a.p, NULL, ctx->base);
  rho_push(ctx, rho_closure(cls));
  if ((err = call(ctx, 0)) < 0)
    return err;
  rho_free(ctx, cls);
  rho_free(ctx, a.p);
  return 0;
}

// int main(int argc, char **argv) {
//   printf("Hello, Rho :)\n");
//   return 0;
// }

#ifdef TEST_ALLOC
#include <assert.h>

int main() {
  printf("Hello, Rho :)\n");

  struct runtime *rt;
  struct context *c1, *c2;

  rt = rho_new(rho_allocator);
  assert(rt);
  c1 = rho_open(rt, 32);
  assert(c1);
  c2 = rho_open(rt, 8);
  assert(c2);

  struct var *v;
  v = rho_alloc(c1, struct var);
  assert(v);
  assert(size(v) == size_expect(v));
  rho_free(c1, v);

  rho_close(c2);
  rho_close(c1);
  rho_drop(rt);
  return 0;
}
#endif

#ifdef TEST_BASIC
#include <assert.h>

int main() {
  // x = 100
  // y = 200
  // print x + y
  // print "Hello, Rho :)"

  // .fun  main
  // .int  40
  // .int  2
  // .str  "Hello, Rho :)"
  u8 buf[] = {
      (u8)OP_pushc, 0x0, // pshc 0 (40)
      (u8)OP_popv,  0x0, // popv  0 (x)
      (u8)OP_pushc, 0x1, // pshc 1 (2)
      (u8)OP_popv,  0x1, // popv  1 (y)
      (u8)OP_pushv, 0x0, // pshv 0 (x)
      (u8)OP_pushv, 0x1, // pshv 1 (y)
      (u8)OP_add,        // add
      (u8)OP_print,      // print
      (u8)OP_pushc, 0x2, // pshc 2 ("Hello, Rho :)")
      (u8)OP_print,      // print
      (u8)OP_ret,        // ret
  };

  struct proto p = {
      .nrefs = 0,
      .nargs = 0,
      .nlocs = 0,
      .buf = buf,
      .consts = ((struct value[]){
          rho_int(40),
          rho_int(2),
          rho_str("Hello, Rho :)"),
      }),
  };

  int n;
  struct runtime *rt;
  struct context *ctx;

  rt = rho_new(rho_allocator);
  ctx = rho_open(rt, 1024);

  rho_push(ctx, rho_closure(closure(ctx, &p, NULL, ctx->base)));
  n = call(ctx, 0);
  assert(n = 1);
  rho_close(ctx);
  rho_drop(rt);
  return 0;
}
#endif

#ifdef TEST_APPEND

#include <assert.h>

int main() {
  struct runtime *rt;
  struct context *ctx;
  rt = rho_new(rho_allocator);
  ctx = rho_open(rt, 1024);

  struct value *p = NULL;
  struct value v[] = {
    rho_int(100),
    rho_float(3.14),
    rho_str("Rho"),
  };
  int i;
  // TODO: segmentation fault at i = 2 :(
  for (i = 0; i < 3; i++) {
    p = rho_append(ctx, p, v+i, 1, struct value);
    printf("len(p) = %ld\n", len(p));
    printf("cap(p) = %ld\n", cap(p));
    printv("p[0]   = ", p);
  }

  rho_close(ctx);
  rho_drop(rt);
  return 0;
}

#endif

#ifdef TEST_ASM

#include <assert.h>

int main() {
  struct runtime *rt;
  struct context *ctx;
  rt = rho_new(rho_allocator);
  ctx = rho_open(rt, 1024);

  struct assembler a = {
    .ctx = ctx,
    .p = rho_alloc(ctx, struct proto),
    .lineno = 0,
    .buf = "pshc 1",
  };

  int err = asm_parse(&a);
  assert(!err);

  rho_close(ctx);
  rho_drop(rt);
  return 0;
}

#endif

#ifdef TEST_REPL

int main() {
  struct runtime *rt;
  struct context *ctx;

  rt = rho_new(rho_allocator);
  ctx = rho_open(rt, 1024);

  printf("exit with status %d\n", repl(ctx));

  rho_close(ctx);
  rho_drop(rt);
  return 0;
}

#endif