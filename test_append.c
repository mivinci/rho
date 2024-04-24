#include "rho.h"
#include <stdio.h>

int main(void) {
  rho_runtime *R;
  rho_context *ctx;
  char *a, *s;
  int n, i, j;

  R = rho_default();
  ctx = rho_open(R, 4096);

  a = 0;
  s = "rho ";

  for (i = 0; i < 6; i++) {
    a = rho_appendgc(ctx, a, s, 1, 4);
    n = rho_len(a);
    printf("%d ", n);
    for (j = 0; j < n; j++)
      printf("%s", a + j * 4);
    printf("\n");
  }
  return 0;
}
