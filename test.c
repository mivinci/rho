#include <assert.h>

#include "rho.h"

int hello(rho_context *ctx, int narg) {
  printf("the ultimate answer to the universe is %d\n",
         rho_popint(ctx) + rho_popint(ctx));  // pop 2 arguments off the stack
  rho_panic(ctx, "everything is good");
  printf("unreachable\n");
  return 0;
}

int main(void) {
  rho_runtime *R;
  rho_context *ctx;

  R = rho_default();  // create a rho runtime using the default allocator
  assert(R);

  ctx = rho_open(R, 1024);  // open a rho context of stack size 1kiB
  assert(ctx);

  rho_pushcproto(ctx, hello);  // push hello onto the stack
  rho_pushint(ctx, 40);        // push 40 onto the stack
  rho_pushint(ctx, 2);         // push 2 onto the stack

  rho_call(ctx, 2);  // call hello(40, 2)

  rho_close(ctx);  // close the rho context
  return 0;
}
