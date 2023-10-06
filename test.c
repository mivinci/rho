#include <assert.h>

#include "rho.h"

int hello(rho_context *ctx, int narg) {
  printf("hello rho :) narg = %d\n", narg);
  rho_panic(ctx, "everything is fine");
  printf("unreachable\n");
  return 0;
}

int main(void) {
  int n;

  rho_context *ctx;
  ctx = rho_open(1024);
  assert(ctx);

  rho_pushcproto(ctx, hello);
  n = rho_call(ctx, 0);
  assert(n == 0);

  rho_close(ctx);
  return 0;
}
