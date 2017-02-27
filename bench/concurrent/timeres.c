#include <time.h>
#include <fcntl.h>
#include <stdio.h>
#include <unistd.h>
#include <stdint.h>
#include <stdlib.h>
#include <math.h>

const clockid_t CLOCK = CLOCK_MONOTONIC;
// const clockid_t CLOCK = CLOCK_PROCESS_CPUTIME_ID;
// const clockid_t CLOCK = CLOCK_THREAD_CPUTIME_ID;

void openfile() {
  int fd = open("/etc/passwd", O_RDONLY);
  close(fd);
}

int main(int argc, char *argv[]) {
  if (argc < 2) {
    fprintf(stderr, "Usage: %s iterations\n", argv[0]);
    return 1;
  }

  struct timespec res;
  clock_getres(CLOCK, &res);
  printf("res: %ldns\n", res.tv_nsec);
  struct timespec start, finish;

  // some warmup
  for (int i = 0; i < 10; i++) {
    openfile();
  }

  clock_gettime(CLOCK, &start);
  const int iters = atoi(argv[1]);
  for (int i = 0; i < iters; i++) {
    openfile();
  }
  clock_gettime(CLOCK, &finish);

  int64_t elapsed = 
      (int64_t) (finish.tv_sec - start.tv_sec) * 1000000000 +
      (int64_t) (finish.tv_nsec - start.tv_nsec);
  printf("ns/open: %ldns\n", elapsed/iters);
  return 0;
}
