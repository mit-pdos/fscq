#include <fcntl.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <time.h>
#include <stdint.h>

typedef struct {
  struct timespec start;
} measurement;

measurement init_measurement() {
  measurement m;
  clock_gettime(CLOCK_MONOTONIC, &m.start);
  return m;
}

void finish_measurement(const measurement m) {
  struct timespec finish;
  clock_gettime(CLOCK_MONOTONIC, &finish);
  int64_t ns = (int64_t) (finish.tv_sec - m.start.tv_sec)*1e9 +
    (int64_t) (finish.tv_nsec - m.start.tv_nsec);
  printf("%ld\n", ns);
}

int main(int argc, char *argv[]) {
  if (argc < 5) {
    fprintf(stderr, "Usage: fsops <stat|open> <path> <reps> <iters>\n");
    return 1;
  }
  char *op = argv[1];
  char *path = argv[2];
  char *reps_s = argv[3];
  char *iters_s = argv[4];

  int reps = atoi(reps_s);
  int iters = atoi(iters_s);
  if (reps <= 0 || iters <= 0) {
    fprintf(stderr, "kiters and reps should be above 0\n");
    return 1;
  }

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
