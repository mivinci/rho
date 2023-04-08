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
*/

#include <stdio.h>

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
#define rho_free(c, p) (freegc(c, p))

#define rho_lock(c) nop
#define rho_unlock(c) nop

#define rho_panic(c, ...) c->rt->panic(c, __VA_ARGS__)

#define anyvalue(p, t) ((struct value){.tag = t, .u.ptr = p})
#define closurevalue(p) anyvalue(p, RHO_CLOSURE)
#define protovalue(p) anyvalue(p, RHO_PROTO)
#define cprotovalue(p) anyvalue(p, RHO_CPROTO)

#define getany(v, t) ((t)(v)->u.ptr)
#define getclosure(v) getany(v, struct closure *)
#define getproto(v) getany(v, struct proto *)
#define getcproto(v) getany(v, cproto)

#define tag(v) (v->tag)

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
    void *ptr;
  } u;
};

struct header {
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
  usize nbuf;         // number of bytecodes.
  usize ncons;        // number of constants.
  usize nrefs;        // number of references.
  usize nargs;        // number of arguments.
  usize nlocs;        // number of local variables.
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
  struct runtime *rt;
  struct ref *openrefs;
  struct value *base;
  struct value *top;
};

struct runtime {
  struct context *threads;
  struct allocator allocator;
  struct header *allocated[RHO_PMAX];
  void (*panic)(struct context *, const char *, ...);
};

typedef int (*cproto)(struct context *, int);

static void *allocgc(struct context *ctx, usize size) {
  struct header *hdr;
  rho_lock(ctx);

  rho_unlock(ctx);
  return hdr->ptr;
}

static void freegc(struct context *ctx, void *ptr) {
  struct header *hdr;
  rho_lock(ctx);

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

int main() {
  printf("Hello, Rho!\n");
  return 0;
}
