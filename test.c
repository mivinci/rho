#include <assert.h>

#include "rho.h"

int hello(rho_context *ctx, int narg) {
  printf("hello rho :) narg = %d\n", narg);
  rho_panic(ctx, "everything is good");
  printf("unreachable\n");
  return 0;
}

int main(void) {
  rho_runtime *R;
  rho_context *ctx;

  R = rho_new(NULL);
  assert(R);

  ctx = rho_open(R, 1024);
  assert(ctx);

  rho_pushcproto(ctx, hello);

  assert(rho_call(ctx, 0) == 0);

  rho_close(ctx);
  return 0;
}
