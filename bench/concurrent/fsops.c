#include <fcntl.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <time.h>

static const clockid_t CLOCK_ID = CLOCK_MONOTONIC;

void report_time(struct timespec start) {
  struct timespec finish;
  clock_gettime(CLOCK_ID, &finish);
  double total_ns = (double) (finish.tv_sec - start.tv_sec)*1e9 + (double) (finish.tv_nsec - start.tv_nsec);
  printf("%lf\n", total_ns);
}

int main(int argc, char *argv[]) {
  if (argc < 4) {
    fprintf(stderr, "Usage: fsops <stat|open> <path> <kiters>\n");
    return 1;
  }
  char *op = argv[1];
  char *path = argv[2];
  char *kiters_s = argv[3];

  int iters = atoi(kiters_s) * 1000;
  if (iters <= 0) {
    fprintf(stderr, "kiters should be above 0\n");
    return 1;
  }

  if (strcmp(op, "stat") == 0) {
    struct timespec start;
    clock_gettime(CLOCK_ID, &start);
    struct stat buf;
    for (int i = 0; i < iters; i++) {
      stat(path, &buf);
    }
    report_time(start);
    return 0;
  }
  if (strcmp(op, "open") == 0) {
    struct timespec start;
    clock_gettime(CLOCK_ID, &start);
    for (int i = 0; i < iters; i++) {
      int fd = open(path, O_RDONLY);
      if (fd > 0) {
        close(fd);
      }
    }
    report_time(start);
    return 0;
  }
  return 1;
}
