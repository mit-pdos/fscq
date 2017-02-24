#include <fcntl.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <time.h>
#include <stdint.h>
#include <math.h>

typedef struct {
  struct timespec start;
} measurement;

typedef struct {
  int n;
  double mean;
  double sum_squares;
} statistics;

measurement init_measurement() {
  measurement m;
  clock_gettime(CLOCK_MONOTONIC, &m.start);
  return m;
}

statistics init_stats() {
  statistics s = {0, 0.0, 0.0};
  return s;
}

void update_statistics(const measurement m, statistics *stats) {
  struct timespec finish;
  clock_gettime(CLOCK_MONOTONIC, &finish);
  double ns = (double) (finish.tv_sec - m.start.tv_sec)*1e9 +
    (double) (finish.tv_nsec - m.start.tv_nsec);
  stats->n += 1;
  double delta = ns - stats->mean;
  stats->mean += delta/stats->n;
  double delta2 = ns - stats->mean;
  stats->sum_squares += delta*delta2;
}

double variance(const statistics stats) {
  if (stats.n < 2) {
    return NAN;
  }
  return stats.sum_squares / (stats.n - 1);
}

void report_time(const statistics stats) {
  double total_ns = stats.mean * stats.n;
  double kiter_variance = variance(stats);
  double iter_stddev_ns = sqrt(kiter_variance)/1000;
  printf("%lf %lf\n", total_ns, iter_stddev_ns);
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
    statistics stats = init_stats();
    struct stat buf;
    for (int i = 0; i < kiters; i++) {
      measurement m = init_measurement();
      for (int j = 0; j < 1000; j++) {
        stat(path, &buf);
      }
      update_statistics(m, &stats);
    }
    report_time(stats);
    return 0;
  }
  if (strcmp(op, "open") == 0) {
    statistics stats = init_stats();
    for (int i = 0; i < kiters; i++) {
      measurement m = init_measurement();
      for (int j = 0; j < 1000; j++) {
        int fd = open(path, O_RDONLY);
        if (fd > 0) {
          close(fd);
        }
      }
      update_statistics(m, &stats);
    }
    report_time(stats);
    return 0;
  }
  return 1;
}
