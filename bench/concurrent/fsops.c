#include <fcntl.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

#include "timing.h"

int main(int argc, char *argv[]) {
  if (argc < 6) {
    fprintf(stderr, "Usage: fsops <stat|open> <pwd> <path> <reps> <iters>\n");
    return 1;
  }
  char *op = argv[1];
  char *desired_wd = argv[2];
  char *path = argv[3];
  char *reps_s = argv[4];
  char *iters_s = argv[5];

  int reps = atoi(reps_s);
  int iters = atoi(iters_s);
  if (reps <= 0 || iters <= 0) {
    fprintf(stderr, "reps %s and iters %s should be above 0\n", reps_s, iters_s);
    return 1;
  }

  chdir(desired_wd);


  if (strcmp(op, "stat") == 0) {
    struct stat buf;
    for (int i = 0; i < iters; i++) {
      measurement m = init_measurement();
      for (int j = 0; j < reps; j++) {
        stat(path, &buf);
      }
      finish_measurement(m);
    }
    return 0;
  }
  if (strcmp(op, "open") == 0) {
    for (int i = 0; i < iters; i++) {
      measurement m = init_measurement();
      for (int j = 0; j < reps; j++) {
        int fd = open(path, O_RDONLY);
        if (fd > 0) {
          close(fd);
        }
      }
      finish_measurement(m);
    }
    return 0;
  }

  fprintf(stderr, "unknown operation %s\n", op);
  return 1;
}
