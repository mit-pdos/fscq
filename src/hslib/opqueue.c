#include "opqueue.h"
#include <stdlib.h>
#include <stdio.h>
#include <errno.h>

#define QUEUE_MAX_SIZE 100

typedef struct {
  operation **ops;
  int length;
  pthread_mutex_t m;
} queue;

queue q = {NULL, 0, PTHREAD_MUTEX_INITIALIZER};

void initialize() {
  q.ops = calloc(sizeof(operation*), QUEUE_MAX_SIZE);
}

operation* get_op() {
  while (1) {
    pthread_mutex_lock(&q.m);
    if (q.length > 0) {
      operation *op = q.ops[q.length-1];
      q.length--;
      pthread_mutex_unlock(&q.m);
      return op;
    }
    pthread_mutex_unlock(&q.m);
  }
}

void send_result(operation *op, int err) {
  op->err = err;
  pthread_cond_signal(&op->cond);
  return;
}

int execute(operation *op) {
  pthread_cond_init(&op->cond, NULL);
  pthread_mutex_init(&op->m, NULL);

  pthread_mutex_lock(&q.m);
  if (q.length >= QUEUE_MAX_SIZE) {
    // we should avoid this happening
    fprintf(stderr, "too many pending operations\n");
    return EAGAIN;
  } else {
    q.ops[q.length] = op;
    q.length++;
  }
  pthread_mutex_unlock(&q.m);

  pthread_mutex_lock(&op->m);
  pthread_cond_wait(&op->cond, &op->m);
  pthread_mutex_unlock(&op->m);
  return op->err;
}
