#include <stdio.h>

#include "rho.h"

int main(void) {
  rho_runtime *R;
  rho_context *ctx;
  char *a, *s;
  int n, i;

  R = rho_default();
  ctx = rho_open(R, 4096);

  a = 0;
  s = "rho ";


  for (i = 0; i < 100; i++)
    a = rho_appendgc(ctx, a, s, 1, 5);
  
  n = rho_len(a);
  for (i = 0; i < n; i++)
    printf("%2d %s\n", i, a+i*5);
  return 0;
}
