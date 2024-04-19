#include "rho.h"
#include <stdio.h>

int main(int argc, char **argv) {
  rho_runtime *R;
  rho_context *ctx;
  rho_closure *cls;
  rho_value v;
  int n;

  if (argc < 2) {
    fprintf(stderr, "Usage: %s [source]", argv[0]);
    return 1;
  }

  R = rho_default();
  ctx = rho_open(R, 4096); /* stack size */

  cls = rho_parse(ctx, argv[1]);
  rho_assert(cls);

  rho_pushclosure(ctx, cls);
  n = rho_call(ctx, 0);
  rho_assert(n == 1);

  v = rho_pop(ctx);
  rho_println(ctx, &v);

  rho_close(ctx);
}
