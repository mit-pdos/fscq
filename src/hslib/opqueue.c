#include "opqueue.h"
#include <stdlib.h>
#include <stdio.h>
#include <errno.h>

static inline uint64_t __attribute__((__always_inline__))
rdtsc(void)
{
    uint32_t a, d;
    __asm __volatile("rdtsc" : "=a" (a), "=d" (d));
    return ((uint64_t) a) | (((uint64_t) d) << 32);
}

#define QUEUE_MAX_SIZE 256

struct queue {
  struct operation *ops[QUEUE_MAX_SIZE];
  int puts;
  int gets;
  pthread_spinlock_t spin;
};

static struct {
  struct queue *queues;
  int num_queues;
} opqueue;

struct operation* get_op(int queue_index) {
  struct queue *q = &opqueue.queues[queue_index];
  while (1) {
    if (q->puts <= q->gets) {
      __sync_synchronize();
      continue;
    }

    pthread_spin_lock(&q->spin);
    if (q->puts <= q->gets) {
      pthread_spin_unlock(&q->spin);
      continue;
    }

    struct operation *op = q->ops[q->gets % QUEUE_MAX_SIZE];
    q->gets++;
    pthread_spin_unlock(&q->spin);
    return op;
  }
}

void send_result(struct operation *op, int err) {
  op->err = err;
  __sync_synchronize();
  op->done = 1;
}

int execute(struct operation *op) {
  op->done = 0;
  struct queue *q = &opqueue.queues[rand()%opqueue.num_queues];

  while (1) {
    if (q->puts - q->gets >= QUEUE_MAX_SIZE) {
      __sync_synchronize();
      continue;
    }

    pthread_spin_lock(&q->spin);
    if (q->puts - q->gets >= QUEUE_MAX_SIZE) {
      pthread_spin_unlock(&q->spin);
      continue;
    }

    q->ops[q->puts % QUEUE_MAX_SIZE] = op;
    q->puts++;
    pthread_spin_unlock(&q->spin);
    break;
  }

  while (!op->done) {
    __sync_synchronize();
  }

  return op->err;
}

struct operation*
send_result_and_get_op(struct operation *op, int err, int queue_index)
{
  send_result(op, err);
  return get_op(queue_index);
}

void
initialize(int num_queues)
{
  opqueue.num_queues = num_queues;
  opqueue.queues = (struct queue*) calloc(num_queues, sizeof(struct queue));
  for (int i = 0; i < num_queues; i++) {
    struct queue *q = &opqueue.queues[i];
    pthread_spin_init(&q->spin, PTHREAD_PROCESS_PRIVATE);
  }
}
