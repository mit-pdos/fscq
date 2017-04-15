#include "parallelize.h"
#include <pthread.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
  action *act;
  int iters;
} operation;

void* do_operation(void *arg) {
  operation *op = (operation *) arg;
  for (int i = 0; i < op->iters; i++) {
    op->act();
  }
  return NULL;
}

void parallel(int par, int iters, action act) {
  pthread_t *threads = (pthread_t*) calloc(par, sizeof(pthread_t *));

  operation op = {act, iters};

  for (int i = 0; i < par; i++) {
    pthread_create(&threads[i], NULL, do_operation, (void*) &op);
    char name[20];
    snprintf(buf, sizeof(buf), "parallel() %d", i);
    pthread_setname_np(threads[i], name);
  }

  for (int i = 0; i < par; i++) {
    pthread_join(threads[i], NULL);
  }
}
