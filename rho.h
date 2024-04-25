#ifndef RHO_H
#define RHO_H

#ifdef __cplusplus
extern "C" {
#endif

#ifdef __STDC__
#include <stdbool.h>
#else
#define bool  int
#define true  1
#define false 0
#endif

#ifndef noreturn
#define noreturn __attribute__((noreturn))
#endif

#include <assert.h>
#define rho_assert(e) assert(e)

#define rho_lock(c)
#define rho_unlock(c)

#define rho_int(v)     ((rho_value){.tag = RHO_INT, .u.i = v})
#define rho_float(v)   ((rho_value){.tag = RHO_FLOAT, .u.f = v})
#define rho_any(p, t)  ((rho_value){.tag = t, .u.ptr = p})
#define rho_ptr(p)     rho_any(p, RHO_PTR)
#define rho_proto(p)   rho_any(p, RHO_PROTO)
#define rho_cproto(p)  rho_any(p, RHO_CPROTO)
#define rho_closure(p) rho_any(p, RHO_CLOSURE)

#define rho_toint(p)    ((p).u.i)
#define rho_tofloat(p)  ((p).u.f)
#define rho_toptr(p)    ((p).u.ptr)
#define rho_toany(p, t) ((t)rho_toptr(p))

#define rho_allocex(c, t, e)      rho_allocgc(c, sizeof(t) + e)
#define rho_alloc(c, t)           rho_allocex(c, t, 0)
#define rho_free(c, p)            rho_freegc(c, p)
#define rho_append(c, d, s, n, t) ((t *)rho_appendgc(c, d, s, n, sizeof(t)))

#define rho_println(c, p) rho_printv(c, p, '\n')

#define rho_pushint(c, n)     rho_push(c, rho_int(n))
#define rho_pushfloat(c, v)   rho_push(c, rho_float(v))
#define rho_pushptr(c, v)     rho_push(c, rho_ptr(p))
#define rho_pushcproto(c, p)  rho_push(c, rho_cproto(p))
#define rho_pushproto(c, p)   rho_push(c, rho_proto(p))
#define rho_pushclosure(c, p) rho_push(c, rho_closure(p))
#define rho_popint(c)         rho_toint(rho_pop(c))
#define rho_popfloat(c)       rho_tofloat(rho_pop(c))
#define rho_popptr(c)         rho_toptr(rho_pop(c))

#define RHO_INT     0
#define RHO_FLOAT   1
#define RHO_BOOL    2
#define RHO_PTR     3
#define RHO_CSTR    4
#define RHO_PROTO   5
#define RHO_CPROTO  6
#define RHO_CLOSURE 7

typedef struct rho_runtime rho_runtime;
typedef struct rho_context rho_context;
typedef struct rho_value rho_value;
typedef struct rho_parser rho_parser;
typedef struct rho_var rho_var;
typedef struct rho_ref rho_ref;
typedef struct rho_type rho_type;
typedef struct rho_proto rho_proto;
typedef struct rho_closure rho_closure;
typedef struct rho_header rho_header;
typedef struct rho_string rho_string;
typedef void *(*rho_allocator)(void *, int);
typedef int (*rho_cproto)(rho_context *, int);

struct rho_value {
  int tag;
  union {
    long i;
    double f;
    void *ptr;
  } u;
};

rho_runtime *rho_default(void);
rho_runtime *rho_new(rho_allocator);
rho_context *rho_open(rho_runtime *, int);
void rho_close(rho_context *);
rho_closure *rho_load(rho_context *, const char *);
rho_closure *rho_parse(rho_context *, const char *);
int rho_dump(rho_context *, rho_closure *);
int rho_call(rho_context *, int);
void rho_panic(rho_context *, const char *, ...);
bool rho_eq(rho_context *, rho_value *, rho_value *);
void rho_push(rho_context *, rho_value);
rho_value rho_pop(rho_context *);
rho_value rho_cast(rho_context *, rho_value *, int);
int rho_printv(rho_context *, rho_value *, char);
void *rho_allocgc(rho_context *, int);
void *rho_callocgc(rho_context *, int, int);
void rho_freegc(rho_context *, void *);
void *rho_appendgc(rho_context *, void *, void *, int, int);
int rho_cap(void *);
int rho_len(void *);
int rho_strcmp(rho_string *, rho_string *);

#ifdef __cplusplus
}
#endif

#endif
