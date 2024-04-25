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

int repl(rho_context *ctx) {
  /* TODO */
  return 0;
}

int main(int argc, char **argv) {
  rho_runtime *r;
  rho_context *ctx;
  rho_closure *cls;
  rho_value v;
  int n, op;
  char *path;

  while ((op = getopt(argc, argv, "hcde")) >= 0) {
    switch (op) {
    case 'c':
    case 'd':
    case 'e':
      break;
    case 'h':
      help(argv);
      exit(0);
    case '?':
      fprintf(stderr, "rho: unknown option %c\n", op);
      exit(1);
    default:
      fprintf(stderr, "rho: bad option %c\n", op);
      exit(1);
    }
  }

  r = rho_default();
  ctx = rho_open(r, 4096);
  path = argv[optind];
  if (path) {
    switch (op) {
    case 'c':
      cls = rho_load(ctx, path);
      rho_assert(cls);
      n = rho_dump(ctx, cls);
      rho_assert(n >= 0);
      break;
    case 'd':
      break;
    default:
      cls = rho_load(ctx, path);
      rho_assert(cls);
      rho_pushclosure(ctx, cls);
      n = rho_call(ctx, 0);
      rho_assert(n >= 0);
      v = rho_pop(ctx);
      rho_println(ctx, &v);
    }
    goto defer;
  }

  repl(ctx);

defer:
  rho_close(ctx);
  return 0;
}
