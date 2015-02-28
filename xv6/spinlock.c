// Mutual exclusion spin locks.

#include "types.h"
#include "defs.h"
#include "param.h"
#ifndef FUSEFS
#include "x86.h"
#include "memlayout.h"
#include "mmu.h"
#include "proc.h"
#endif
#include "spinlock.h"

void
initlock(struct spinlock *lk, char *name)
{
  lk->name = name;
  lk->locked = 0;
  lk->cpu = 0;
}

// Acquire the lock.
// Loops (spins) until the lock is acquired.
// Holding a lock for a long time may cause
// other CPUs to waste time spinning to acquire it.
void
acquire(struct spinlock *lk)
{
}

// Release the lock.
void
release(struct spinlock *lk)
{
}

void
wakeup(void* addr) {
}

void
sleep(void* addr, struct spinlock* lk) {
}
