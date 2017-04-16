#ifndef OPQUEUE_H
#define OPQUEUE_H
#include <sys/stat.h>
#include <pthread.h>

typedef struct {
  char *path;
  struct stat *attr;
  pthread_mutex_t m;
  pthread_cond_t cond;
  int err;
  int done;
} operation;

operation* get_op();

void send_result(operation *op, int err);

int execute(operation *op);

#endif
