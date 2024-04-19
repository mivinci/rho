#include "rho.h"

int main(void) {
  rho_runtime *R;
  rho_context *ctx;
  rho_closure *cls;

  R = rho_default();
  ctx = rho_open(R, 4096);

  cls = rho_load(ctx, "test.rho");
  rho_assert(cls);

  rho_close(ctx);
}
