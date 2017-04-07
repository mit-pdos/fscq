#include <time.h>
#include <stdio.h>
#include <stdint.h>

typedef struct {
  struct timespec start;
} measurement;

measurement init_measurement() {
  measurement m;
  clock_gettime(CLOCK_MONOTONIC, &m.start);
  return m;
}

int64_t elapsed_ns(const measurement m) {
  struct timespec finish;
  clock_gettime(CLOCK_MONOTONIC, &finish);
  int64_t ns = (int64_t) (finish.tv_sec - m.start.tv_sec)*1e9 +
    (int64_t) (finish.tv_nsec - m.start.tv_nsec);
  return ns;
}

void finish_measurement(const measurement m) {
  int64_t ns = elapsed_ns(m);
  printf("%ld\n", ns);
}
