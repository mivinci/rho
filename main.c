#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include "rho.h"

void help(char **argv) {
  fprintf(stdout,
          "Usage: %s [options] [path]\n"
          "Options:\n"
          "  -h    print this help message\n"
          "  -c    compile mode\n"
          "  -d    disassemble mode\n"
          "  -e    eval mode\n",
          argv[0]);
}


int main(int argc, char **argv) {
  rho_runtime *r;
  rho_context *ctx;
  rho_closure *cls;
  rho_value v;
  int n, op;

  r = rho_default();
  ctx = rho_open(r, 4096);

  while ((op = getopt(argc, argv, "hcde")) >= 0) {
    switch (op) {
    case 'h':
      help(argv);
      exit(0);
    case '?':
      fprintf(stderr, "rho: unknown option %c\n", op);
      exit(1);
    case 'c':
      cls = rho_load(ctx, argv[optind]);
      rho_assert(cls);
      n = rho_dump(ctx, cls, stdout);
      rho_assert(n >= 0);
      goto defer;
    case 'd':
      goto defer;
    case 'e':
      goto defer;
    }
  }

  cls = rho_load(ctx, argv[optind]);
  rho_assert(cls);
  rho_pushclosure(ctx, cls);
  n = rho_call(ctx, 0);
  rho_assert(n >= 0);
  v = rho_pop(ctx);
  rho_println(ctx, &v);

defer:
  rho_close(ctx);
  return 0;
}
