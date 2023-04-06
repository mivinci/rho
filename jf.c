#include <stdlib.h>

//
#include "jf.h"
#include "list.h"

#define value_i32(n) ((struct value){.tag = JF_i32, .u.__i32 = n})
#define as_function(v) ((struct function *)v.u.obj)

#define read_u8(b) (*b++)
#define read_u16(b) (b += 2, *(u16 *)b - 2)

enum tag {
  JF_i32,
  JF_f64,
  JF_function,
};

enum opcode {
  OP_load_const8,
  OP_load_const16,
  OP_load,
  OP_load_deref,
  OP_store,
  OP_store_deref,
  OP_call,
  OP_ret,
};

struct value {
  enum tag tag;
  union {
    i32 __i32;
    f64 __f64;
    void *obj;
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

struct upvalue {
  struct value *ref;
  struct value val;
};

struct function {
  struct string name;
  bool is_cfn;
  i8 nargs;
  usize len;
  union {
    u8 *codes;
    struct value (*proto)(struct context *, struct value *, usize);
  } u;
  struct upvalue *upvals;
};

struct trace {
  struct trace *prev;
  struct function *fn;
  struct value *vars; // local variables
};

struct context {
  struct list_head node;
  struct value *base;
  struct value *top;
  struct trace *trace;
  struct runtime *rt;
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
};

struct runtime *jf_calloc(struct allocator al, usize n, usize size) {
  struct runtime *rt;
  usize cap = n * size;
  if (!(rt = al.alloc(sizeof(*rt) + cap)))
    return NULL;
  rt->size = size;
  rt->cap = cap;
  rt->base = (struct value *)rt + sizeof(*rt);
  rt->avail = rt->base;
  rt->top = rt->base;
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
  if (rt->top - rt->base >= rt->cap)
    return NULL;
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

static void *allocgc(struct runtime *rt, usize sz) {
  if (sz > (1 << 10))
    return rt->allocator.alloc(sz);
  // TODO: allocate from memory pool if the requested size is less than 1kB.
}

static void freegc(struct runtime *rt, void *ptr, usize size) {}

static void panic(struct context *ctx, const char fmt, ...) {
  struct trace *tr;
  for (tr = ctx->trace; tr = tr->prev; tr) {
  }
}

static struct value compile(struct context *ctx, const char src) {}

static struct value eval(struct context *ctx, const char src,
                         struct value *args, u8 n) {
  return call(ctx, compile(ctx, src), args, n);
}

static struct value call(struct context *ctx, struct value val,
                         struct value *args, u8 n) {
  struct function *fn;
  struct value *top, *vars, ra;
  struct trace tr;
  u8 *pc;
  u32 n;

  if (val.tag != JF_function)
    panic(ctx, "type %d is not callable.", val.tag);

  fn = as_function(val);
  if (fn->nargs > 0 && fn->nargs != n)
    panic(ctx, "function %s expects %d arguments but %d were given.",
          fn->name.buf, fn->nargs, n);

  if (fn->is_cfn)
    return fn->u.proto(ctx, args, n);

  
  top = ctx->top;
  vars = top;

  tr.fn = fn;
  tr.vars = vars;
  tr.prev = ctx->trace;
  ctx->trace = &tr;

  pc = fn->u.codes;

  for (;;) {
    switch (read_u8(pc)) {
    case OP_load_const8:
      n = read_u8(pc);
      *top++ = value_i32(n);
      break;
    case OP_load_const16:
      n = read_u16(pc);
      *top++ = value_i32(n);
      break;
    case OP_load:
      n = read_u8(pc);
      *top++ = *(vars + n);
      break;
    case OP_store:
      n = read_u8(pc);
      *(vars + n) = *(top - 1); // TODO: do we really have to?
      break;
    case OP_call:
      n = read_u8(pc);
      ra = *(top - n - 1);
      ctx->top = top;
      ra = call(ctx, ra, top - n, n);
      *top++ = ra; // push
      break;
    case OP_ret:
      ra = *(--top); // pop
      ctx->trace = tr.prev;
      return ra;
    }
  }
}