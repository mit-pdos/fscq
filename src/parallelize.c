#include "parallelize.h"
#include <pthread.h>
#include <stdlib.h>

void* call_action(void *arg) {
  action *act = (action *) arg;
  (*act)();
  return NULL;
}

void noop() {
  return;
}

void parallel(int n, action act) {
  pthread_t *threads = (pthread_t*) calloc(n, sizeof(pthread_t *));

  for (int i = 0; i < n; i++) {
    pthread_create(&threads[i], NULL, call_action, (void*) act);
  }

  for (int i = 0; i < n; i++) {
    pthread_join(threads[i], NULL);
  }
}
