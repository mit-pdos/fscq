#include <stdlib.h>
#include <stdio.h>
#include <fcntl.h>
#include <unistd.h>
#include "timing.h"

int main(int argc, char *argv[]) {
  if (argc < 3) {
    fprintf(stderr, "usage: %s <iters> <file>\n", argv[0]);
    return 1;
  }
  int iters = atoi(argv[1]);
  char *path = argv[2];

  measurement m = init_measurement();

  char buf[4096];
  for (int i = 1; i < iters; i++) {
    int fd = open(path, O_RDONLY);
    if (fd < 0) {
      fprintf(stderr, "could not open %s for reading\n", path);
      return 1;
    }
    while (read(fd, &buf, 4096) > 0) { }
    close(fd);
  }

  finish_measurement(m);
}
