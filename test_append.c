#include "rho.h"

int main(void) {
  rho_runtime *R;
  rho_context *ctx;
  char *a, c;
  int n, i, j;

  R = rho_default();
  ctx = rho_open(R, 4096);

  a = 0;
  c = 'A';

  for (j = 0; j < 6; j++) {
    a = rho_appendgc(ctx, a, &c, 1, 1);
    n = len(a);
    printf("%d ", n);
    for (i = 0; i < n; i++)
      printf("%c ", a[i]);
    printf("\n");
  }
  return 0;
}
