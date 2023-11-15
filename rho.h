#ifndef RHO_H
#define RHO_H

#include <stdio.h>

#define RHO_INT     0
#define RHO_FLT     1
#define RHO_PTR     2
#define RHO_STR     3
#define RHO_PROTO   4
#define RHO_CPROTO  5
#define RHO_CLOSURE 6

#define rho_nop       ((void)0)
#define rho_assert(e) rho_nop

#define rho_int(v)     ((struct value){.tag = RHO_INT, .u.i = v})
#define rho_float(v)   ((struct value){.tag = RHO_FLT, .u.f = v})
#define rho_any(p, t)  ((struct value){.tag = t, .u.ptr = p})
#define rho_ptr(p)     rho_any(p, RHO_PTR)
#define rho_proto(p)   rho_any(p, RHO_PROTO)
#define rho_cproto(p)  rho_any(p, RHO_CPROTO)
#define rho_closure(p) rho_any(p, RHO_CLOSURE)

#define rho_toint(p)    ((p).u.i)
#define rho_tofloat(p)  ((p).u.f)
#define rho_toptr(p)    ((p).u.ptr)
#define rho_toany(p, t) ((t)rho_toptr(p))

#define rho_push(c, v) __rho_push(c, v)
#define rho_pop(c)     __rho_pop(c)

#define rho_lock(c)   rho_nop
#define rho_unlock(c) rho_nop

#define rho_allocex(c, t, e)      ((t *)__rho_allocgc(c, sizeof(t) + e))
#define rho_alloc(c, t)           rho_allocex(c, t, 0)
#define rho_free(c, p)            __rho_freegc(c, p)
#define rho_append(c, d, s, n, t) ((t *)__rho_append(c, d, s, n, sizeof(t)))

typedef unsigned char u8;
typedef unsigned short u16;
typedef unsigned int u32;
typedef int i32;
typedef float f32;
typedef size_t usize;

typedef struct context rho_context;
typedef struct runtime rho_runtime;

typedef int (*cproto)(struct context *, int);
typedef void *(*rho_allocator)(void *, size_t);

struct value {
  int tag;
  union {
    long i;
    double f;
    void *ptr;
  } u;
};

// creates a runtime using the default allocator.
struct runtime *rho_default();
// creates a rho runtime. the default rho allocator implemented using malloc,
// realloc and free in stdlib.h will be used if the given one is NULL.
struct runtime *rho_new(rho_allocator);
// opens a rho context from a non-NULL rho runtime with a stack size.
struct context *rho_open(struct runtime *, int);
// closes a rho context and, if the last, frees up the underlying rho runtime.
void rho_close(struct context *);

// traces back through stack frames, writes them to stderr and calls exit(1).
void rho_panic(struct context *, const char *, ...);
// raises an error to a rho context.
void rho_error(struct context *, const char *, ...);
// given the number of arguments on the stack, calls a value right below those
// arguments and returns the number of values returned by the callee.
int rho_call(struct context *, int);

struct value __rho_pop(struct context *);
void __rho_push(struct context *, struct value);
void *__rho_allocgc(struct context *, usize);
void __rho_freegc(struct context *, void *);
void *__rho_append(struct context *, void *, void *, usize, usize);

#define rho_pushint(c, v)     rho_push(c, rho_int(v))
#define rho_pushfloat(c, v)   rho_push(c, rho_float(v))
#define rho_pushptr(c, v)     rho_push(c, rho_ptr(p))
#define rho_pushcproto(c, p)  rho_push(c, rho_cproto(p))
#define rho_pushproto(c, p)   rho_push(c, rho_proto(p))
#define rho_pushclosure(c, p) rho_push(c, rho_closure(p))

#define rho_popint(c)   rho_toint(rho_pop(c))
#define rho_popfloat(c) rho_tofloat(rho_pop(c))
#define rho_popptr(c)   rho_toptr(rho_pop(c))

#endif  // RHO_H
