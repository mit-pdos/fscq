#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>
#include "timing.h"

typedef struct {
  char *fname;
  int64_t elapsed_ns;
} readop;

void *large_read(void *arg) {
  readop *op = (readop*) arg;
  int f = open(op->fname, O_RDONLY);
  if (f < 0) {
    pthread_exit(NULL);
  }
  char buf[4096];

  measurement m = init_measurement();
  for (int i = 0; i < 2500; i++) {
    pread(f, buf, sizeof(buf), i*4096);
  }
  op->elapsed_ns = elapsed_ns(m);
  close(f);
  pthread_exit(NULL);
}

void *small_read(void *arg) {
  readop *op = (readop*) arg;
  measurement m = init_measurement();
  char buf[4096];
  for (int i = 0; i < 2500; i++) {
    int f = open(op->fname, O_RDONLY);
    if (f < 0) {
      pthread_exit(NULL);
    }
    pread(f, buf, sizeof(buf), 0);
    close(f);
  }
  op->elapsed_ns = elapsed_ns(m);
  pthread_exit(NULL);
}

int main() {
  readop large_fn = {"/tmp/fscq/large-10m"};
  readop small_fn = {"/tmp/fscq/small-4k"};
  pthread_t large_t, small_t;
  pthread_create(&large_t, NULL, large_read, (void *)&large_fn);
  pthread_create(&small_t, NULL, small_read, (void *)&small_fn);
  pthread_join(large_t, NULL);
  pthread_join(small_t, NULL);

  printf("large\t%ld\n", large_fn.elapsed_ns);
  printf("small\t%ld\n", small_fn.elapsed_ns);
  pthread_exit(NULL);
}
