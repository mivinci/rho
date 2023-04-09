/*
fn a(x) {
  fn b(y) {
    fn c(z) {
      x + y + z
    }
  }
}

main: load_const   0 (proto)
      closure
      store_var    0 (a)
      ret
a:    load_var     0 (x)
      load_const   1 (proto)
      closure
      store_var    1 (b)
      ret
b:    load_var     0 (y)
      load_const   1 (proto)
      closure
      store_var    1 (c)
      ret
c:    load_var     0 (z)
      load_ref     0 (x)
      load_ref     1 (y)
      load_var     0 (z)
      add
      add
      ret


1+2

main: load_const   0 (1)
      load_const   1 (2)
      add
*/

#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>

#include "list.h"

#define u8 unsigned char
#define u16 unsigned short
#define u32 unsigned int
#define i64 long long
#define f64 double
#define usize size_t

#define RHO_PMAX 10

#define nop ((void)0)

#define rho_allocex(c, t, e) ((t *)allocgc(c, sizeof(t) + e))
#define rho_alloc(c, t) rho_allocex(c, t, 0)
#define rho_free(c, p) freegc(c, p)

#define rho_lock(c) nop
#define rho_unlock(c) nop

#define rho_panic(c, ...) panic(c, __VA_ARGS__)

#define anyvalue(p, t) ((struct value){.tag = t, .u.ptr = p})
#define closurevalue(p) anyvalue(p, RHO_CLOSURE)
#define protovalue(p) anyvalue(p, RHO_PROTO)
#define cprotovalue(p) anyvalue(p, RHO_CPROTO)

#define getany(p, t) ((t)(p)->u.ptr)
#define getclosure(p) getany(p, struct closure *)
#define getproto(p) getany(p, struct proto *)
#define getcproto(p) getany(p, cproto)

#define tag(v) (v->tag)

#define header(p) ((struct header*)((char*)(p)-sizeof(struct header)))
#define cap(p) (header(p)->cap)
#define len(p) (header(p)->len)
#define cap_expect(p) (1 << bits32(sizeof(*(p))))

#define bits32(x) (32 - __builtin_clz(x))

enum opcode {
  OP_closure,
  OP_call,
  OP_ret,
};

enum tag {
  RHO_PROTO,
  RHO_CPROTO,
  RHO_CLOSURE,
};

struct value {
  enum tag tag;
  union {
    i64 i;
    f64 r;
    void *ptr;
  } u;
};

struct header {
  struct header *next;
  u8 marked : 1;
  u8 color : 2;
  usize rc;  // reference count.
  usize cap; // size allocated for ptr.
  usize len; // size used by ptr.
  void *ptr;
};

struct allocator {
  void *(*alloc)(usize);
  void *(*realloc)(void *, usize);
  void (*free)(void *);
};

struct parser {
  struct context *ctx;
  struct proto *proto;
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

void static panic(struct context *ctx, const char *fmt, ...) {
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

void rho_drop(struct runtime *rt) {
  rt->allocator.free(rt);
}

struct runtime *rho_default() {
  struct allocator al = {.alloc = malloc, .realloc = realloc, .free = free};
  return rho_new(al);
}

struct context *rho_open(struct runtime *rt, usize size) {
  struct context *ctx;
  void *ptr;
  if (!(ptr = rt->allocator.alloc(size+sizeof(*ctx))))
    return NULL;
  ctx = (struct context*)ptr;
  ctx->base = (struct value*)(ptr + sizeof(*ctx));
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
    if (!(hdr = rt->allocator.alloc(size+sizeof(*hdr))))
      rho_panic(ctx, "out of memory");
    memset(hdr, 0, sizeof(*hdr));
    hdr->cap = size;
    hdr->ptr = (void*)(hdr+1);
    return hdr->ptr;
  }
  rho_lock(ctx);
  bits = bits32(size);
  hdr = rt->allocated[bits];
  if (!hdr) {
    size = 1 << bits;
    if (!(hdr = rt->allocator.alloc(size+sizeof(*hdr))))
      rho_panic(ctx, "out of memory");
    memset(hdr, 0, sizeof(*hdr));
    hdr->cap = size;
    hdr->ptr = (void*)(hdr+1);
    rho_unlock(ctx);
    return hdr->ptr;
  }
  hdr->len = hdr->rc = 0;
  rt->allocated[bits] = hdr->next;
  rho_unlock(ctx);
  return hdr->ptr;
}

static void freegc(struct context *ctx, void *ptr) {
  struct runtime *rt = ctx->rt;
  struct header *hdr = header(ptr);
  usize bits;
  if (hdr->cap > (1 << RHO_PMAX)) {
    rt->allocator.free(hdr);
    return;
  }
  bits = bits32(hdr->cap);
  rho_lock(ctx);
  hdr->next = rt->allocated[bits];
  rt->allocated[bits] = hdr;
  rho_unlock(ctx);
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

// Given the number of input arguments nargs, call calls TOS and returns the
// number of output arguments, therefore, the base is top - nargs, input
// arguments are [base, top) and the output arguments are [base, n).
int call(struct context *ctx, int nargs) {
  struct value *top, *base, *val;
  struct closure *cls;
  struct ref **refs;
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
  refs = cls->refs;
  while (1) {
    switch (*pc++) {
    case OP_closure:
      top[-1] = closure(ctx, getproto(top - 1), refs, base);
      break;
    case OP_call:
      ctx->top = top;
      top = base + call(ctx, *pc++);
      break;
    case OP_ret:
      return top - base;
    }
  }
}


int parse(struct parser *ps) {
  return 0;
}

int eval(struct context *ctx, const char *s, usize n) {
  struct parser ps;
  struct proto *proto;
  int err;
  proto = rho_alloc(ctx, struct proto);
  ps.proto = proto;
  ps.ctx = ctx;
  if ((err = parse(&ps)) < 0)
    return err;
  *ctx->top++ = closure(ctx, proto, NULL, ctx->base);
  return call(ctx, 1);
}

#include <assert.h>

int main() {
  printf("Hello, Rho :)\n");

  struct runtime *rt;
  struct context *c1, *c2;

  rt = rho_default();
  assert(rt);
  c1 = rho_open(rt, 32);
  assert(c1);
  c2 = rho_open(rt, 8);
  assert(c2);

  struct var *v;
  v = rho_alloc(c1, struct var);
  assert(v);
  assert(cap(v) == cap_expect(v));
  rho_free(c1, v);

  rho_close(c2);
  rho_close(c1);
  rho_drop(rt);
  return 0;
}
