#include "rho.h"

int main(void) {
  rho_runtime *R;
  rho_context *ctx;
  rho_value v;
  int n;

  R = rho_default();
  ctx = rho_open(R, 4096);

  n = rho_load(ctx, "test_expr.rho");
  rho_assert(n == 0);

  n = rho_call(ctx, 0);
  rho_assert(n == 1);

  v = rho_pop(ctx);
  rho_println(ctx, &v);

  rho_close(ctx);
}
