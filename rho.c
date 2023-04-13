/*
fn a(x) {
  fn b(y) {
    fn c(z) {
      x + y + z
    }
  }
}

main: pushc    0 (proto)
      closure
      popv     0 (a)
      ret
a:    pushv    0 (x)
      pushc    1 (proto)
      closure
      popv     1 (b)
      ret
b:    pushv    0 (y)
      pushc    1 (proto)
      closure
      popv     1 (c)
      ret
c:    pushv    0 (z)
      pushr    0 (x)
      pushr    1 (y)
      pushv    0 (z)
      add
      add
      ret


1+2

main: pushc    0 (1)
      pushc    1 (2)
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

#define rho_lock(c) nop
#define rho_unlock(c) nop

#define rho_panic(c, ...) panic(c, __VA_ARGS__)

#define rho_push(c, v) (*c->top++ = v)
#define rho_pop(c) (*(--c->top))

#define tag(p) ((p)->tag)
#define isnum(p) (tag(p) == RHO_INT || tag(p) == RHO_FLT)

#define anyvalue(p, t) ((struct value){.tag = t, .u.ptr = p})
#define closurevalue(p) anyvalue(p, RHO_CLOSURE)
#define protovalue(p) anyvalue(p, RHO_PROTO)
#define cprotovalue(p) anyvalue(p, RHO_CPROTO)
#define strlitvalue(p) anyvalue(p, RHO_STRLIT)
#define intvalue(v) ((struct value){.tag = RHO_INT, .u.i = v})
#define fltvalue(v) ((struct value){.tag = RHO_FLT, .u.r = v})

#define getany(p, t) ((t)(p)->u.ptr)
#define getclosure(p) getany(p, struct closure *)
#define getproto(p) getany(p, struct proto *)
#define getcproto(p) getany(p, cproto)
#define getstrlit(p) getany(p, const char *)
#define getint(p) ((p)->u.i)
#define getflt(p) ((p)->u.r)
#define getnum(p) (tag(p) == RHO_INT ? getint(p) : getflt(p))

#define header(p) ((struct header *)((char *)(p) - sizeof(struct header)))
#define avail(p) (header(p)->avail)
#define size(p) (header(p)->size)
#define size_expect(p) (1 << bits32(sizeof(*(p))))
#define len(p) ((size(p) - avail(p)) / sizeof(*p))
#define cap(p) (size(p) / sizeof(*p))

#define bits32(x) (32 - __builtin_clz(x))
#define max(a, b) ((a) > (b) ? (a) : (b))

#define vmbinop(op, top)                                                       \
  {                                                                            \
    struct value *s = --top - 1;                                               \
    if (tag(s) == RHO_INT)                                                     \
      getint(s) op## = getint(top);                                            \
    else                                                                       \
      getflt(s) op## = getflt(top);                                            \
  }

#define vmjmpop(op, pc, top)                                                   \
  if (getnum(--top) op 0)                                                      \
    pc += (*(u16 *)pc);

enum token {
  TK_UNKNOWN,
  TK_EOF,

};

enum opcode {
  OP_print,   // for debuging, will be removed.
  OP_closure, // pops TOS out to create a closure instance onto the stack.
  OP_call,    // call TOS.
  OP_ret,     // returns to the previous stack frame.
  OP_pushv,   // pushes a variable from var[i] onto the stack.
  OP_pushc,   // pushes a constant from cons[i] onto the stack.
  OP_pushr,   // pushes a reference from ref[i] onto the stack.
  OP_popv,    // pops TOS out to var[i].
  OP_popr,    // pops TOS out to ref[i].
  OP_add,     // pops TOS and adds it to TOS-1.
  OP_sub,     // pops TOS and substracts it from TOS-1.
  OP_cmp,     // pops TOS and TOS-1 and then pushes TOS-(TOS-1) onto the stack.
  OP_jpn,     // moves pc i step forward if TOS < 0
  OP_jpp,     // moves pc i step forward if TOS > 0
  OP_jpz,     // moves pc i step forward if TOS == 0
};

enum tag {
  RHO_INT,
  RHO_FLT,
  RHO_STRLIT,
  RHO_PROTO,
  RHO_CPROTO,
  RHO_CLOSURE,
};

struct value {
  enum tag tag;
  union {
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

struct tokinfo {
  u8 len;
  union {
    i32 i;
    f32 r;
    char *s;
  } u;
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
  u32 name;           // index into runtime::symbols.
  usize np;           // number of child-protos.
  usize nbuf;         // number of bytecodes.
  usize ncons;        // number of constants.
  usize nrefs;        // number of references.
  usize nargs;        // number of arguments.
  usize nlocs;        // number of local variables.
  struct proto **p;   // child-protos defined in this proto.
  struct value *cons; // constants defined in this proto.
  struct var *refs;   // references appeared in this proto.
  struct var *vars;   // variables (arguments and local variables)
                      // defined in this proto.
  u8 *buf;            // bytecode compiled for this proto.
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

struct value closure(struct context *ctx, struct proto *proto,
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
  return closurevalue(cls);
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

static void println(struct value *v) {
  switch (tag(v)) {
  case RHO_INT:
    printf("%ld\n", getint(v));
    break;
  case RHO_FLT:
    printf("%f\n", getflt(v));
    break;
  case RHO_STRLIT:
    printf("%s\n", getstrlit(v));
    break;
  default:
    printf("<object 0x%p>\n", getany(v, void *));
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
      println(top - 1);
      break;
    case OP_closure:
      top[-1] = closure(ctx, getproto(top - 1), cls->refs, base);
      break;
    case OP_call:
      ctx->top = top;
      top = base + call(ctx, *pc++);
      break;
    case OP_ret:
      if (ctx->openrefs)
        closerefs(ctx, base);
      return top - base;
    case OP_pushv:
      *top++ = base[*pc++];
      break;
    case OP_pushc:
      *top++ = cls->proto->cons[*pc++];
      break;
    case OP_pushr:
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
  rho_push(ctx, closure(ctx, &proto, NULL, ctx->base));
  return call(ctx, 0);
}

static inline void bufwrite(struct context *ctx, u8 **p, u8 *buf, usize n) {
  struct header *hdr = header(*p);
  if (hdr->avail < n)
    *p = reallocgc(ctx, *p, max(n, hdr->size * 3 / 2));
  memcpy(*p, buf, n);
  hdr->avail -= n;
}

static void emit8(struct context *ctx, u8 **p, u8 c) {
  bufwrite(ctx, p, &c, 1);
}

static void emit16(struct context *ctx, u8 **p, u16 c) {
  bufwrite(ctx, p, (u8 *)&c, 2);
}

struct assembler {
  struct context *ctx;
  struct proto *p;
  const char *buf;
  int lineno;
};

static void asm_syntaxerror(struct assembler *as, const char *fmt, ...) {
  va_list ap;
  char buf[64];
  sprintf(buf, "syntax error at line %d: %s\n", as->lineno, fmt);
  va_start(ap, fmt);
  vfprintf(stderr, buf, ap);
  va_end(ap);
}

int asm_parse(struct assembler *as) {
  const char *s = as->buf;
  struct proto *p = as->p;
  int err, op, n = 0;
  char c;

  while ((c = *s++) != 0) {
    switch (c) {
    case ' ':
    case '\t':
    case '\n':
      if (c == '\n')
        as->lineno++;
      break;
    case '.':
      if (strncmp(s, "fun", 3) == 0) {
        s += 3;
        while (*s++ == ' ')
          ;
        p->cons = rho_allocex(as->ctx, struct value, atoi(s));
      } else if (strncmp(s, "int", 3) == 0) {
        s += 3;
        while (*s++ == ' ')
          ;
        p->cons[n++] = intvalue(atoi(s));
      } else if (strncmp(s, "flt", 3)) {
        s += 3;
        while (*s++ == ' ')
          ;
        p->cons[n++] = fltvalue(atof(s));
      } else {
        asm_syntaxerror(as, "unexpected token");
        return 1;
      }
      while (*s++ != '\n')
        ;
      break;
    case 'p':
      if (*s++ == 'u' && *s++ == 's' && *s++ == 'h') {
        switch (*s++) {
        case 'c':
          op = OP_pushc;
          break;
        case 'v':
          op = OP_pushv;
          break;
        case 'r':
          op = OP_pushr;
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
      } else if (strncmp(s, "rint", 4) == 0) {
        s += 4;
        emit8(as->ctx, &p->buf, (u8)OP_print);
        while (*s++ != '\n')
          ;
        continue;
      } else {
        asm_syntaxerror(as, "unexpected token");
        return 1;
      }
      while (*s++ == ' ')
        ;
      emit8(as->ctx, &p->buf, (u8)op);
      emit8(as->ctx, &p->buf, (u8)atoi(s));
      while (*s++ != '\n')
        ;
      break;
    default:
      if (strncmp(s, "add", 3) == 0) {
        s += 3;
        op = OP_add;
      } else if (strncmp(s, "ret", 3) == 0) {
        s += 3;
        op = OP_ret;
      } else {
        asm_syntaxerror(as, "unexpected token");
        return 1;
      }
      emit8(as->ctx, &p->buf, (u8)op);
      while (*s++ != '\n')
        ;
    }
  }
  p->nbuf = len(p->buf);
  p->ncons = len(p->cons);
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
      (u8)OP_pushc, 0x0, // pushc 0 (40)
      (u8)OP_popv,  0x0, // popv  0 (x)
      (u8)OP_pushc, 0x1, // pushc 1 (2)
      (u8)OP_popv,  0x1, // popv  1 (y)
      (u8)OP_pushv, 0x0, // pushv 0 (x)
      (u8)OP_pushv, 0x1, // pushv 1 (y)
      (u8)OP_add,        // add
      (u8)OP_print,      // print
      (u8)OP_pushc, 0x2, // pushc 2 ("Hello, Rho :)")
      (u8)OP_print,      // print
      (u8)OP_ret,        // ret
  };

  struct proto p = {
      .nrefs = 0,
      .nargs = 0,
      .nlocs = 0,
      .ncons = 2,
      .np = 0,
      .nbuf = 11,
      .buf = buf,
      .cons = ((struct value[]){
          intvalue(40),
          intvalue(2),
          strlitvalue("Hello, Rho :)"),
      }),
  };

  int n;
  struct runtime *rt;
  struct context *ctx;

  rt = rho_new(rho_allocator);
  ctx = rho_open(rt, 1024);

  rho_push(ctx, closure(ctx, &p, NULL, ctx->base));
  n = call(ctx, 0);
  assert(n = 1);

  rho_close(ctx);
  rho_drop(rt);
  return 0;
}
#endif

int main() {
  struct assembler as;
  struct runtime *rt;
  struct context *ctx;
  rt = rho_new(rho_allocator);
  ctx = rho_open(rt, 1024);
  as.buf = ".fun 3";
  as.ctx = ctx;
  as.p = rho_alloc(ctx, struct proto);
  as.lineno = 0;
  asm_parse(&as);
  rho_close(ctx);
  rho_drop(rt);
  return 0;
}
