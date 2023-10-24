#include <stdarg.h>
#include <stdlib.h>
#include <string.h>

#include "list.h"
#include "rho.h"

#define PMAX 10

#define tag(p)      ((p)->tag)
#define isnumber(p) (tag(p) == RHO_INT || tag(p) == RHO_FLT)

#define push(c, v) (*c->top++ = v)
#define pop(c)     (*(--c->top))

#define header(p) ((struct header *)((char *)(p) - sizeof(struct header)))
#define len(p) ((header(p)->size) - (header(p)->avail)) / sizeof(*p))
#define cap(p) ((header(p)->size) / sizeof(*p))

#define bits32(x) (32 - __builtin_clz(x))
#define max(a, b) ((a) > (b) ? (a) : (b))

#define tocproto(p)  rho_toany(p, cproto)
#define toproto(p)   rho_toany(p, struct proto *)
#define toclosure(p) rho_toany(p, struct closure *)

#define binop(ctx, op, top)                                                    \
  {                                                                            \
    struct value *p = --top - 1;                                               \
    switch (tag(p)) {                                                          \
    case RHO_INT:                                                              \
      rho_toint(p) op## = rho_toint(top);                                      \
      break;                                                                   \
    case RHO_FLT:                                                              \
      rho_tofloat(p) op## = rho_tofloat(top);                                  \
      break;                                                                   \
    default:                                                                   \
      rho_panic(ctx, "invalid operand(s)");                                    \
    }                                                                          \
  }

#define binop_int(ctx, op, top)                                                \
  {                                                                            \
    struct value *p = --top - 1;                                               \
    switch (tag(p)) {                                                          \
    case RHO_INT:                                                              \
      rho_toint(p) op## = rho_toint(top);                                      \
      break;                                                                   \
    default:                                                                   \
      rho_panic(ctx, "invalid operand(s)");                                    \
    }                                                                          \
  }

#define jmpop(op, pc, top)                                                     \
  {                                                                            \
    struct value *p = --top;                                                   \
    if ((tag(p) == RHO_INT ? rho_toint(p) : rho_tofloat(p)) op 0)              \
      pc += (*(u16 *)pc);                                                      \
  }

struct var {
  int islocal : 1;
  int isconst : 1;
  u16 idx;  // index into proto::vars if var::islocal or closure::refs of the
            // enclosing closure.
};

struct proto {
  int nref;
  int narg;
  int nloc;
  struct proto **p;
  struct value *consts;
  struct var *refs;
  struct var *vars;  // arguments and local variables.
  u8 *buf;           // bytecode.

  int row;
  int col;
};

struct ref {
  struct ref *next;
  struct value *pv;
  struct value v;
};

struct closure {
  struct proto *proto;
  struct ref **refs;
};

struct trace {
  struct list_head node;
  struct value *base;
  int narg;
};

struct context {
  struct list_head node;
  struct list_head trace;
  struct runtime *rt;
  struct ref *refs;  // open refs.
  struct value *base;
  struct value *top;
};

struct runtime {
  int len;
  rho_allocator alloc;
  struct list_head contexts;
  struct header *freelists[PMAX];
};

struct header {
  struct header *next;
  int marked : 1;
  int color  : 2;
  int rc;       // reference counter.
  usize size;   // size allocated for header::ptr.
  usize avail;  // size unused.
  void *ptr;
};

struct runtime *rho_new(rho_allocator alloc) {
  struct runtime *rt;
  if (!alloc)
    alloc = __alloc;
  if (!(rt = alloc(NULL, sizeof(*rt))))
    return NULL;
  rt->alloc = alloc;
  rt->len = 0;
  list_head_init(&rt->contexts);
  return rt;
}

struct context *rho_open(struct runtime *rt, int size) {
  struct context *ctx;
  void *ptr;
  if (!(ptr = rt->alloc(NULL, size + sizeof(*ctx))))
    return NULL;
  ctx = (struct context *)ptr;
  ctx->base = (struct value *)(ptr + sizeof(*ctx));
  ctx->top = ctx->base;
  ctx->refs = NULL;
  ctx->rt = rt;
  list_head_init(&ctx->trace);
  rho_lock(ctx);
  list_add(&ctx->node, &rt->contexts);
  rt->len++;
  rho_unlock(ctx);
  return ctx;
}

void rho_close(struct context *ctx) {
  struct runtime *rt = ctx->rt;
  list_del(&ctx->node);
  rt->alloc(ctx, 0);
  rho_lock(ctx);
  if (rt->len <= 0)
    rt->alloc(rt, 0);
  rho_unlock(ctx);
}

static void *allocgc(struct context *ctx, usize size) {
  struct runtime *rt = ctx->rt;
  struct header *hdr;
  usize bits;
  if (size > (1 << PMAX)) {
    if (!(hdr = rt->alloc(NULL, size + sizeof(*hdr))))
      rho_panic(ctx, "out of memory");
    memset(hdr, 0, sizeof(*hdr));
    hdr->size = size;
    hdr->avail = hdr->size;
    hdr->ptr = (void *)(hdr + 1);
    return hdr->ptr;
  }
  rho_lock(ctx);
  bits = bits32(size);
  hdr = rt->freelists[bits];
  if (!hdr) {
    size = 1 << bits;
    if (!(hdr = rt->alloc(NULL, size + sizeof(*hdr))))
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
  rt->freelists[bits] = hdr->next;
  rho_unlock(ctx);
  return hdr->ptr;
}

static void freegc(struct context *ctx, void *ptr) {
  struct runtime *rt = ctx->rt;
  struct header *hdr = header(ptr);
  usize bits;
  if (hdr->size > (1 << PMAX)) {
    rt->alloc(hdr, 0);
    return;
  }
  bits = bits32(hdr->size);
  rho_lock(ctx);
  hdr->next = rt->freelists[bits];
  rt->freelists[bits] = hdr;
  rho_unlock(ctx);
}

static void *reallocgc(struct context *ctx, void *ptr, usize newsize) {
  struct runtime *rt = ctx->rt;
  struct header *hdr = header(ptr), *newhdr;
  if (newsize > (1 << PMAX)) {
    if (!(hdr = rt->alloc(hdr, newsize + sizeof(*hdr))))
      rho_panic(ctx, "out of memory");
    hdr->size = newsize;
    hdr->avail += newsize - hdr->size;
    hdr->ptr = (void *)(hdr + 1);
    return hdr->ptr;
  }
  newhdr = header(allocgc(ctx, newsize));
  memcpy(newhdr->ptr, hdr->ptr, hdr->size);
  freegc(ctx, hdr->ptr);
  return newhdr->ptr;
}

static void *append(struct context *ctx, void *dst, void *src, usize n,
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
  hdr = header(dst);  // we have to re-gain the header in case of a reallocgc.
  memcpy(dst + (hdr->size - hdr->avail), src, ncopy);
  hdr->avail -= ncopy;
  return dst;
}

static struct ref *findref(struct context *ctx, struct value *lv) {
  struct ref *p, **pp = &ctx->refs;  // pp is my favorite pointer trick
  while ((p = *pp) && p->pv >= lv) {
    if (p->pv == lv)
      return p;
    pp = &p->next;
  }
  p = rho_alloc(ctx, struct ref);
  p->pv = lv;
  p->next = *pp;
  *pp = p;
  return p;
}

static void closerefs(struct context *ctx, struct value *lv) {
  struct ref *p = ctx->refs;
  while (p && p->pv > lv) {
    p->v = *p->pv;
    p->pv = &p->v;
    p = p->next;
    ctx->refs = p;
  }
}

static struct closure *alloc_closure(struct context *ctx, struct proto *proto,
                                     struct ref **refs, struct value *base) {
  struct closure *cls;
  struct var *ref;
  int i, nref = proto->nref;
  cls = rho_allocex(ctx, struct closure, nref);
  rho_assert(cls);
  cls->proto = proto;
  cls->refs = (struct ref **)(cls + 1);
  for (i = 0; i < nref; i++) {
    ref = proto->refs + i;
    if (ref->islocal)
      cls->refs[i] = findref(ctx, base + ref->idx);
    else
      cls->refs[i] = refs[ref->idx];
  }
  return cls;
}

enum opcode {
  OP_rsvd,   // reserved.
  OP_print,  // for debuging, will be removed.
  OP_cls,    // pops TOS out to create a closure instance onto the stack.
  OP_call,   // call TOS.
  OP_ret,    // returns to the previous stack frame.
  OP_pshv,   // pushes a variable from var[i] onto the stack.
  OP_pshc,   // pushes a constant from cons[i] onto the stack.
  OP_pshr,   // pushes a reference from ref[i] onto the stack.
  OP_popv,   // pops TOS out to var[i].
  OP_popr,   // pops TOS out to ref[i].
  OP_add,    // TOS-1 += TOS, pops out TOS.
  OP_sub,    // TOS-1 -= TOS, pops out TOS.
  OP_mul,    // TOS-1 *= TOS, pops out TOS.
  OP_div,    // TOS-1 /= TOS, pops out TOS.
  OP_mod,    // TOS-1 %= TOS, pops out TOS.
  OP_and,    // TOS-1 &= TOS, pops out TOS.
  OP_or,     // TOS-1 |= TOS, pops out TOS.
  OP_xor,    // TOS-1 ^= TOS, pops out TOS.
  OP_shl,    // TOS-1 <<= TOS, pops out TOS.
  OP_shr,    // TOS-1 >>= TOS, pops out TOS.
  OP_cmp,    // pops TOS and TOS-1 and then pushes TOS-(TOS-1) onto the stack.
  OP_jpn,    // moves pc i step(s) forward if TOS < 0
  OP_jpp,    // moves pc i step(s) forward if TOS > 0
  OP_jpz,    // moves pc i step(s) forward if TOS == 0
};

static int fprintv(FILE *fp, struct value *p) {
  switch (tag(p)) {
  case RHO_INT:
    return fprintf(fp, "%ld", rho_toint(p));
  case RHO_FLT:
    return fprintf(fp, "%lf", rho_tofloat(p));
  default:
    return fprintf(fp, "<object 0x%p>", rho_toptr(p));
  }
}

void rho_error(struct context *ctx, const char *fmt, ...) {}

void rho_panic(struct context *ctx, const char *fmt, ...) {
  struct list_head *p;
  struct trace *trace;
  struct value *callee;
  struct closure *cls;
  va_list ap;
  list_foreach_prev(p, &ctx->trace) {
    trace = container_of(p, struct trace, node);
    callee = trace->base - 1;
    switch (tag(callee)) {
    case RHO_CPROTO:
      fprintf(stderr, "<cproto %p>\n", tocproto(callee));
      break;
    case RHO_CLOSURE:
      cls = toclosure(callee);
      fprintf(stderr, "<closure %p> %d:%d\n", cls, cls->proto->row,
              cls->proto->col);
      break;
    }
    fprintf(stderr,
            "  base = %p\n"
            "  narg = %d\n",
            trace->base, trace->narg);
  }
  fprintf(stderr, "panic: ");
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  putc('\n', stderr);
  va_end(ap);
  exit(EXIT_FAILURE);
}

int rho_call(struct context *ctx, int narg) {
  struct trace trace;
  struct value *top, *base, *p;
  struct closure *cls, *tmp;
  u8 *pc;
  top = ctx->top;
  base = top - narg;
  p = base - 1;
  trace.base = base;
  trace.narg = narg;
  list_add(&trace.node, &ctx->trace);
  if (tag(p) == RHO_CPROTO)
    return tocproto(p)(ctx, narg);
  if (tag(p) != RHO_CLOSURE)
    rho_panic(ctx, "not callable");
  cls = toclosure(p);
  if (cls->proto->narg > narg)
    rho_panic(ctx, "missing %d argument(s)", cls->proto->narg - narg);
  pc = cls->proto->buf;
  while (1) {
    switch (*pc++) {
    case OP_print:
      fprintv(stdout, top - 1);
      break;
    case OP_cls:
      tmp = alloc_closure(ctx, toproto(top - 1), cls->refs, base);
      top[-1] = rho_closure(tmp);
      break;
    case OP_call:
      ctx->top = top;
      top = base + rho_call(ctx, *pc++);
      break;
    case OP_ret:
      if (ctx->refs)
        closerefs(ctx, base);
      list_del(&trace.node);
      return top - base;
    case OP_pshv:
      *top++ = base[*pc++];
      break;
    case OP_pshc:
      *top++ = cls->proto->consts[*pc++];
      break;
    case OP_pshr:
      *top++ = *(cls->refs[*pc++]->pv);
      break;
    case OP_popv:
      base[*pc++] = *(--top);
      break;
    case OP_popr:
      cls->refs[*pc++]->pv = --top;
      break;
    case OP_add:
      binop(ctx, +, top);
      break;
    case OP_sub:
      binop(ctx, -, top);
      break;
    case OP_mul:
      binop(ctx, *, top);
      break;
    case OP_div:
      binop(ctx, /, top);
      break;
    case OP_mod:
      binop_int(ctx, %, top);
      break;
    case OP_and:
      binop_int(ctx, &, top);
      break;
    case OP_or:
      binop_int(ctx, |, top);
      break;
    case OP_xor:
      binop_int(ctx, ^, top);
      break;
    case OP_shl:
      binop_int(ctx, <<, top);
      break;
    case OP_shr:
      binop_int(ctx, >>, top);
      break;
    case OP_cmp:
      if (isnumber(top - 1) && isnumber(top - 2))
        binop(ctx, -, top);
      break;
    case OP_jpn:
      jmpop(<, pc, top);
      break;
    case OP_jpp:
      jmpop(>, pc, top);
      break;
    case OP_jpz:
      jmpop(==, pc, top);
      break;
    }
  }
}

static void *__alloc(void *ptr, size_t size) {
  if (size == 0)
    free(ptr);
  else if (ptr)
    return realloc(ptr, size);
  else
    return malloc(size);
}

void __rho_push(struct context *ctx, struct value v) { push(ctx, v); }
struct value __rho_pop(struct context *ctx) { return pop(ctx); }
void *__rho_allocgc(struct context *ctx, usize sz) { return allocgc(ctx, sz); }
void __rho_freegc(struct context *ctx, void *p) { freegc(ctx, p); }
void *__rho_append(struct context *ctx, void *dst, void *src, usize n,
                   usize usz) {
  return append(ctx, dst, src, n, usz);
}
