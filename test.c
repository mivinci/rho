#include <assert.h>

#include "rho.h"

int hello(struct context *ctx, int narg) {
  printf("hello rho :) narg = %d\n", narg);
  rho_panic(ctx, "everything is fine");
  return 0;
}

int main(void) {
  int n;
  struct runtime *rt;
  struct context *ctx;
  rt = rho_new(rho_allocator);
  assert(rt);
  ctx = rho_open(rt, 4*1024);
  assert(ctx);

  rho_pushcproto(ctx, hello);
  n = rho_call(ctx, 0);
  assert(n == 0);

  rho_close(ctx);
  return 0;
}
