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

static pthread_spinlock_t spin;
static int request;
static int reply;

static uint64_t t1, t2, t3, t4;

static void*
thr1(void* arg)
{
  int myreq;

  for (;;) {
    t1 = rdtsc();

    pthread_spin_lock(&spin);
    request += 1;
    myreq = request;
    pthread_spin_unlock(&spin);

    while (reply != myreq) {
      __sync_synchronize();
    }

    t4 = rdtsc();

    printf("timing: %ld %ld %ld\n", t2-t1, t3-t2, t4-t3);
  }
}

static void*
thr2(void *arg)
{
  int myreply;

  for (;;) {
    while (request == myreply) {
      __sync_synchronize();
    }

    t2 = rdtsc();

    pthread_spin_lock(&spin);
    myreply = request;
    reply = myreply;
    pthread_spin_unlock(&spin);

    t3 = rdtsc();
  }
}

int
main(int ac, char** av)
{
  pthread_spin_init(&spin, PTHREAD_PROCESS_PRIVATE);
  pthread_t tid;
  pthread_create(&tid, 0, &thr1, 0);
  pthread_create(&tid, 0, &thr2, 0);
  sleep(1);
}
