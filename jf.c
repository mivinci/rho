#include <stdlib.h>
#include <string.h>

//
#include "jf.h"
#include "list.h"

#define value_i32(n) ((struct value){.tag = JF_i32, .u.__i32 = n})
#define value_function(f) ((struct value){.tag = JF_function, .u.ptr = f})
#define as_function(v) ((struct function *)v.u.ptr)

#define read_u8(b) (*b++)
#define read_u16(b) (b += 2, *(u16 *)b - 2)

enum tag {
  JF_i32,
  JF_f64,
  JF_function,
};

enum opcode {
  OP_load_const,
  OP_load_fast,
  OP_load_deref,
  OP_store_fast,
  OP_store_deref,
  OP_make_ref,
  OP_make_function,
  OP_call,
  OP_ret,
};

/* compile time representations */

struct value_def {
  bool escaped : 1;
};

/* runtime representations */

struct value {
  enum tag tag;
  union {
    i32 __i32;
    f64 __f64;
    void *ptr;
  } u;
};

struct string {
  bool islit;
  u32 hash;
  u32 len;
  u8 buf[1];
};

struct map {
  usize cap;
  usize len;
  struct value *keys;
  struct value *values;
};

struct tuple {
  usize cap;
  struct value **refs;
};

struct array {
  usize cap;
  usize len;
  u8 *buf;
};

struct function {
  struct string name;
  bool is_cfn;
  i8 nargs;
  union {
    struct array *codes;
    struct value (*proto)(struct context *, struct value *, usize);
  } u;
  usize nrefs;
  usize nconsts;
  struct value *consts;
  struct value **refs;  // pre-allocated at compile time.
};

struct context {
  struct list_head node;
  struct value *base;
  struct value *top;
  struct runtime *rt;
};

struct chunk {
  struct chunk *next;
  usize rc;  // reference count
  usize size;
  void *ptr;
};

struct runtime {
  usize cap;
  usize size;
  struct value *base;
  struct value *avail;
  struct value *top;
  struct list_head ctx;
  struct map symbols;
  struct allocator allocator;
  struct chunk *pool[JF_PEXP];  // memory pool divided to chunks of size: 2B,
                                // 4B, 8B, ..., 1024B.
};

struct runtime *jf_calloc(struct allocator al, usize n, usize size) {
  struct runtime *rt;
  usize cap = n * size;
  if (!(rt = al.alloc(sizeof(*rt) + cap))) return NULL;
  rt->size = size;
  rt->cap = cap;
  rt->base = (u8*)rt + sizeof(*rt);
  rt->avail = rt->base;
  rt->top = rt->base;
  memset(rt->pool, 0, JF_PEXP);
  list_head_init(&rt->ctx);
  return rt;
}

void jf_free(struct runtime *rt) {
  struct allocator al = rt->allocator;
  al.free(rt);
}

struct runtime *jf_default() {
  struct allocator al = {.alloc = malloc, .realloc = realloc, .free = free};
  return jf_calloc(al, 1, 1024);
}

struct context *jf_open(struct runtime *rt) {
  struct context *ctx;
  if (rt->top - rt->base >= rt->cap) return NULL;
  ctx = (struct context *)rt->avail;
  ctx->base = (struct value *)ctx + sizeof(*ctx);
  ctx->top = ctx->base;
  ctx->rt = rt;
  list_add(&rt->ctx, &ctx->node);
  rt->avail = rt->top;
  rt->top += rt->size;
  return ctx;
}

void jf_close(struct runtime *rt, struct context *ctx) {
  rt->avail = (struct value *)ctx;
  list_del(&ctx->node);
}

// allocgc allocates 'size' bytes from the heap using the runtime allocator if
// 'size' is bigger than 2^JF_PEXP (default: 1kB), otherwise from the runtime
// memory pool.
static void *allocgc(struct context *ctx, usize size) {
  struct runtime *rt = ctx->rt;
  struct chunk *hdr;
  usize bits;  // the number of effective bits of a 32-bit integer.

  if (size > (1 << JF_PEXP)) {
    if (!(hdr = rt->allocator.alloc(size + sizeof(*hdr))))
      panic(ctx, "out of memory");
    hdr->size = size;
    hdr->ptr = (void *)hdr + sizeof(*hdr);
    return hdr->ptr;
  }

  bits = bits32(size);
  hdr = rt->pool[bits];
  if (!hdr) {
    size = 1 << bits;
    if (!(hdr = rt->allocator.alloc(size + sizeof(*hdr))))
      panic(ctx, "out of memory");
    hdr->size = size;
    hdr->ptr = (void *)hdr + sizeof(*hdr);
    return hdr->ptr;
  }

  rt->pool[bits] = hdr->next;
  return hdr->ptr;
}

static void freegc(struct context *ctx, void *ptr) {
  struct runtime *rt = ctx->rt;
  struct chunk *hdr = ptr - sizeof(*hdr);
  usize bits;
  if (hdr->size > (1 << JF_PEXP)) {
    rt->allocator.free(hdr);
    return;
  }
  bits = bits32(hdr->size);
  hdr->next = rt->pool[bits];
  rt->pool[bits] = hdr;
}

static void panic(struct context *ctx, const char fmt, ...) {}

static struct value compile(struct context *ctx, const char src) {}

static struct value eval(struct context *ctx, const char src,
                         struct value *args, u8 n) {
  return call(ctx, compile(ctx, src), args, n);
}

static struct value call(struct context *ctx, struct value val,
                         struct value *args, u8 n) {
  struct function *fn, *rb;
  struct value *top, *vars, *consts, **refs, ra;
  u8 *pc;
  u32 n;

  if (val.tag != JF_function)
    panic(ctx, "type %d is not callable.", val.tag);

  fn = as_function(val);
  if (fn->nargs > 0 && fn->nargs != n)
    panic(ctx, "function %s expects %d arguments but %d were given.",
          fn->name.buf, fn->nargs, n);

  if (fn->is_cfn) return fn->u.proto(ctx, args, n);

  top = ctx->top;
  vars = top;
  consts = fn->consts;
  refs = fn->refs;
  pc = fn->u.codes->buf;

  for (;;) {
    switch (read_u8(pc)) {
      case OP_load_const:
        n = read_u8(pc);
        *top++ = consts[n];
        break;
      case OP_load_fast:
        n = read_u8(pc);
        *top++ = vars[n];
        break;
      case OP_load_deref:
        n = read_u8(pc);
        *top++ = *refs[n];
        break;
      case OP_store_fast:
        n = read_u8(pc);
        *(vars + n) = top[-1];  // TODO: do we really have to?
        break;
      case OP_store_deref:  // NOTE: this opcode expects that location refs + n
                            // to have been allocated by opcode OP_make_ref.
        n = read_u8(pc);
        **(refs + n) = top[-1];
        break;
      case OP_make_ref:
        n = read_u8(pc);
        *(refs + n) = allocgc(ctx, sizeof(struct value));
        break;
      case OP_make_function:
        ra = *(--top);
        rb = as_function(ra);
        memcpy(rb->refs, fn->refs, fn->nrefs);
        ra = value_function(rb);
        *top++ = ra;
        break;
      case OP_call:
        n = read_u8(pc);
        ra = *(top - n - 1);
        ctx->top = top;
        ra = call(ctx, ra, top - n, n);
        *top++ = ra;  // push
        break;
      case OP_ret:
        ra = *(--top);  // pop
        return ra;
    }
  }
}