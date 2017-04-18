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

  struct {
    int ident;
    uint64_t time;
  } timings[10*1024];
  int next_timing;
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
    op->t2 = rdtsc();
    pthread_spin_unlock(&q->spin);
    op->t2 = rdtsc();
    return op;
  }
}

void send_result(struct operation *op, int err) {
  op->err = err;
  __sync_synchronize();
  op->done = 1;
  op->t3 = rdtsc();
}

int find_unloaded() {
  int i1 = rand()%opqueue.num_queues;
  int i2 = rand()%opqueue.num_queues;
  if ((opqueue.queues[i1].puts - opqueue.queues[i1].gets) <
      (opqueue.queues[i2].puts - opqueue.queues[i2].gets)) {
    return i1;
  } else {
    return i2;
  }
}

void report_time(int ident, int queue, uint64_t start, uint64_t end) {
  struct queue *q = &opqueue.queues[queue];
  int index = q->next_timing++;
  q->timings[index].ident = ident;
  q->timings[index].time = end - start;
}

int execute(struct operation *op) {
  op->t0 = rdtsc();
  op->done = 0;
  int queue_index = find_unloaded();
  struct queue *q = &opqueue.queues[queue_index];

  while (1) {
    pthread_spin_lock(&q->spin);
    if (q->puts - q->gets >= QUEUE_MAX_SIZE) {
      pthread_spin_unlock(&q->spin);
      continue;
    }

    if (q->puts - q->gets >= QUEUE_MAX_SIZE) {
      pthread_spin_unlock(&q->spin);
      continue;
    }

    q->ops[q->puts % QUEUE_MAX_SIZE] = op;
    q->puts++;
    op->t1 = rdtsc();

    pthread_spin_unlock(&q->spin);
    break;
  }

  while (!op->done) {
    __sync_synchronize();
  }

  uint64_t now = rdtsc();
  report_time(0, queue_index, op->t0, op->t1);
  report_time(1, queue_index, op->t1, op->t2);
  report_time(2, queue_index, op->t2, op->t3);
  report_time(3, queue_index, op->t3, now);
  report_time(4, queue_index, now, rdtsc());

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

void
print_opqueue_timings()
{
  for (int qi = 0; qi < opqueue.num_queues; qi++) {
    struct queue *q = &opqueue.queues[qi];
    printf("queue %d: %d puts %d gets\n", qi, q->puts, q->gets);
  }

  for (int qi = 0; qi < opqueue.num_queues; qi++) {
    struct queue *q = &opqueue.queues[qi];
    for (int i = 0; i < q->next_timing; i++) {
      int ident = q->timings[i].ident;
      uint64_t time = q->timings[i].time;
      printf("%d on %d: %lfus\n", ident, qi, ((double) time) / 2600);
    }
  }
}
