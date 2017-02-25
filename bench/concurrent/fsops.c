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
  if (argc < 4) {
    fprintf(stderr, "Usage: fsops <stat|open> <path> <kiters>\n");
    return 1;
  }
  char *op = argv[1];
  char *path = argv[2];
  char *kiters_s = argv[3];

  int kiters = atoi(kiters_s);
  if (kiters <= 0) {
    fprintf(stderr, "kiters should be above 0\n");
    return 1;
  }

  if (strcmp(op, "stat") == 0) {
    struct stat buf;
    for (int i = 0; i < kiters; i++) {
      measurement m = init_measurement();
      for (int j = 0; j < 1000; j++) {
        stat(path, &buf);
      }
      finish_measurement(m);
    }
    return 0;
  }
  if (strcmp(op, "open") == 0) {
    for (int i = 0; i < kiters; i++) {
      measurement m = init_measurement();
      for (int j = 0; j < 1000; j++) {
        int fd = open(path, O_RDONLY);
        if (fd > 0) {
          close(fd);
        }
      }
      finish_measurement(m);
    }
    return 0;
  }
  return 1;
}
