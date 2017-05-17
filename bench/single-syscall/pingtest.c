#include <stdio.h>
#include <pthread.h>
#include <stdint.h>
#include <unistd.h>

static inline uint64_t __attribute__((__always_inline__))
rdtsc(void)
{
  uint32_t a, d;
  __asm __volatile("rdtsc" : "=a" (a), "=d" (d));
  return ((uint64_t) a) | (((uint64_t) d) << 32);
}

static pthread_mutex_t mu;
static pthread_cond_t cv;
static int request;
static int reply;

static uint64_t t0, t1, t2, t3, t4;

static void*
thr1(void* arg)
{
  int myreq;

  for (;;) {
    t1 = rdtsc();

    pthread_mutex_lock(&mu);
    request++;
    myreq = request;
    pthread_cond_signal(&cv);
    while (reply != myreq) {
      pthread_cond_wait(&cv, &mu);
    }
    pthread_mutex_unlock(&mu);

    t4 = rdtsc();

    printf("timing: %ld %ld %ld\n", t2-t1, t3-t2, t4-t3);
  }
}

static void*
thr2(void *arg)
{
  int myreply;

  pthread_mutex_lock(&mu);
  for (;;) {
    while (request == myreply)
      pthread_cond_wait(&cv, &mu);

    t2 = rdtsc();

    myreply = request;
    reply = myreply;
    pthread_cond_signal(&cv);

    t3 = rdtsc();
  }
}

int
main(int ac, char** av)
{
  pthread_t tid;
  pthread_create(&tid, 0, &thr1, 0);
  pthread_create(&tid, 0, &thr2, 0);
  sleep(1);
}
