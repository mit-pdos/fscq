#include "opqueue.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <errno.h>

static inline uint64_t __attribute__((__always_inline__))
rdtsc(void)
{
    uint32_t a, d;
    __asm __volatile("rdtsc" : "=a" (a), "=d" (d));
    return ((uint64_t) a) | (((uint64_t) d) << 32);
}

#define QUEUE_MAX_SIZE 256
#define MAX_TIMING (1000*1024)

struct queue {
  struct operation *ops[QUEUE_MAX_SIZE];
  int puts;
  int gets;
  pthread_spinlock_t spin;

  struct {
    int ident;
    uint64_t time;
  } timings[MAX_TIMING];
  int next_timing;
};

static struct {
  struct queue *qs;
  int num_queues;
} opqueue;

struct operation* get_op(int qi) {
  struct queue *q = &opqueue.qs[qi];

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
    op->t1 = rdtsc();
    pthread_spin_unlock(&q->spin);
    return op;
  }
}

void send_result(struct operation *op, int err) {
  op->err = err;
  __sync_synchronize();
  op->t3 = rdtsc();
  op->done = 1;
}

void report_time(int ident, int qi, uint64_t start, uint64_t end) {
  struct queue *q = &opqueue.qs[qi];
  int index = q->next_timing++;
  if (index < MAX_TIMING) {
    q->timings[index].ident = ident;
    q->timings[index].time = end - start;
  }
}

int execute(struct operation *op) {
  if (op->op_type == OP_OPEN &&
      strcmp(op->u.open.pn, "/print_timing_info") == 0) {
    print_opqueue_timings();
  }
  op->done = 0;
  op->t0 = rdtsc();
  int qi = rand()%opqueue.num_queues;
  struct queue *q = &opqueue.qs[qi];

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
    op->t2 = rdtsc();
    pthread_spin_unlock(&q->spin);
    break;
  }

  while (!op->done) {
    __sync_synchronize();
  }

  uint64_t t4 = rdtsc();
  report_time(0, qi, op->t0, op->t1);
  report_time(1, qi, op->t1, op->t2);
  report_time(2, qi, op->t2, op->t3);
  report_time(3, qi, op->t3, t4);

  return op->err;
}

void
initialize(int n)
{
  opqueue.num_queues = n;
  opqueue.qs = (struct queue *) calloc(n, sizeof(struct queue));

  for (int qi = 0; qi < n; qi++) {
    struct queue *q = &opqueue.qs[qi];
    pthread_spin_init(&q->spin, PTHREAD_PROCESS_PRIVATE);
  }
}

void
print_opqueue_timings()
{
  for (int qi = 0; qi < opqueue.num_queues; qi++) {
    struct queue *q = &opqueue.qs[qi];
    printf("queue %d: %d puts %d gets\n", qi, q->puts, q->gets);
  }

  for (int qi = 0; qi < opqueue.num_queues; qi++) {
    struct queue *q = &opqueue.qs[qi];
    for (int i = 0; i < q->next_timing; i++) {
      int ident = q->timings[i].ident;
      uint64_t time = q->timings[i].time;
      printf("%d on %d: %lfus\n", ident, qi, ((double) time) / 2600);
    }
  }
}
