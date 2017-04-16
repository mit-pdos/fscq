#include "opqueue.h"
#include <stdlib.h>
#include <stdio.h>
#include <errno.h>

#define QUEUE_MAX_SIZE 256

static struct {
  struct operation *ops[QUEUE_MAX_SIZE];
  int puts;
  int gets;
  pthread_mutex_t m;
  pthread_cond_t wait_empty;
  pthread_cond_t wait_full;
} q;

struct operation* get_op() {
  pthread_mutex_lock(&q.m);
  while (1) {
    if (q.puts > q.gets) {
      struct operation *op = q.ops[q.gets % QUEUE_MAX_SIZE];
      q.gets++;
      pthread_cond_signal(&q.wait_full);
      pthread_mutex_unlock(&q.m);
      return op;
    } else {
      pthread_cond_wait(&q.wait_empty, &q.m);
    }
  }
}

void send_result(struct operation *op, int err) {
  pthread_mutex_lock(&op->m);
  op->err = err;
  op->done = 1;
  pthread_cond_signal(&op->cond);
  pthread_mutex_unlock(&op->m);
  return;
}

int execute(struct operation *op) {
  pthread_cond_init(&op->cond, NULL);
  pthread_mutex_init(&op->m, NULL);
  op->done = 0;

  pthread_mutex_lock(&q.m);
  while (q.puts - q.gets >= QUEUE_MAX_SIZE) {
    pthread_cond_wait(&q.wait_full, &q.m);
  }

  q.ops[q.puts % QUEUE_MAX_SIZE] = op;
  q.puts++;
  pthread_cond_signal(&q.wait_empty);
  pthread_mutex_unlock(&q.m);

  pthread_mutex_lock(&op->m);
  while (!op->done) {
    pthread_cond_wait(&op->cond, &op->m);
  }
  pthread_mutex_unlock(&op->m);
  return op->err;
}
