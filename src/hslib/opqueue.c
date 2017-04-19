#include "opqueue.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <errno.h>
#include <signal.h>

static inline uint64_t __attribute__((__always_inline__))
rdtsc(void)
{
    uint32_t a, d;
    __asm __volatile("rdtsc" : "=a" (a), "=d" (d));
    return ((uint64_t) a) | (((uint64_t) d) << 32);
}

#define MAX_TIMING (1000*1024)

struct queue {
  struct operation *op;
  int num_ops;

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
    struct operation *op = q->op;
    if (op != NULL) {
      // retrieved from queue
      q->op = NULL;
      op->t2 = rdtsc();
      __sync_fetch_and_add(&q->num_ops, 1);
      return op;
    }
    __sync_synchronize();
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
  if (q->next_timing < MAX_TIMING) {
    if (start > end) {
      // sometimes the operation is removed from the queue ~100 cycles before
      // adding it - possibly due to unsychronized processor-local clocks; in
      // these cases, do not add underflowing end-start but don't print an
      // error either
      if (start > end+200) {
        fprintf(stderr, "nonsensical timing %d on %d: %lu - %lu = %ld\n",
            ident, qi,
            end, start, (int64_t) end - (int64_t) start);
      }
      return;
    }
    int index = q->next_timing++;
    q->timings[index].ident = ident;
    q->timings[index].time = end - start;
  }
}

int execute(struct operation *op) {
  op->done = 0;
  op->t0 = rdtsc();

  int qi = rand()%opqueue.num_queues;
  while (1) {
    struct queue *q = &opqueue.qs[qi];
    if (__sync_bool_compare_and_swap(&q->op, NULL, op)) {
      // queue put
      op->t1 = rdtsc();
      break;
    }
    __sync_synchronize();
    qi = (qi+1)%opqueue.num_queues;
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

void sig_handler(int signo) {
  print_opqueue_timings();
}

void
initialize(int n)
{
  opqueue.num_queues = n;
  opqueue.qs = (struct queue *) calloc(n, sizeof(struct queue));
  signal(SIGUSR1, sig_handler);
}

void
print_opqueue_timings()
{
  for (int qi = 0; qi < opqueue.num_queues; qi++) {
    struct queue *q = &opqueue.qs[qi];
    printf("queue %d: %d ops\n", qi, q->num_ops);
  }

  // for (int qi = 0; qi < opqueue.num_queues; qi++) {
  //   struct queue *q = &opqueue.qs[qi];
  //   for (int i = 0; i < q->next_timing; i++) {
  //     int ident = q->timings[i].ident;
  //     uint64_t time = q->timings[i].time;
  //     printf("%d on %d: %lfus\n", ident, qi, ((double) time) / 2600);
  //   }
  // }
  uint64_t total_time[4] = {0, 0, 0, 0};
  for (int qi = 0; qi < opqueue.num_queues; qi++) {
    struct queue *q = &opqueue.qs[qi];
    for (int i = 0; i < q->next_timing; i++) {
      int ident = q->timings[i].ident;
      uint64_t time = q->timings[i].time;
      total_time[ident] += time;
    }
  }
  for (int ident = 0; ident < 4; ident++) {
    printf("total %d time: %lfs\n", ident, ((double) total_time[ident])/3330.0/1e6);
  }

  // clear timings till next call
  for (int qi = 0; qi < opqueue.num_queues; qi++) {
    struct queue *q = &opqueue.qs[qi];
    q->num_ops = 0;
    q->next_timing = 0;
  }
}
