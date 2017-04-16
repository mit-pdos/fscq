#ifndef OPQUEUE_H
#define OPQUEUE_H
#include <sys/stat.h>
#include <pthread.h>
#include <inttypes.h>

struct op_getattr {
  const char *pn;
  struct stat *st;
};

struct op_mknod {
  const char *pn;
  mode_t mode;
  dev_t rdev;
};

struct op_mkdir {
  const char *pn;
  mode_t mode;
};

struct op_unlink {
  const char *pn;
};

typedef enum {
  OP_GETATTR = 1,
  OP_MKNOD = 2,
  OP_MKDIR = 3,
  OP_UNLINK = 4,
} op_t;

struct operation {
  pthread_mutex_t m;
  pthread_cond_t cond;
  int64_t err;
  int done;

  int op_type;

  union {
    struct op_getattr getattr;
    struct op_mknod mknod;
    struct op_mkdir mkdir;
    struct op_unlink unlink;
  } u;
};

struct operation* get_op();

void send_result(struct operation *op, int err);

int execute(struct operation *op);

#endif
