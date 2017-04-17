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

struct op_open {
  const char *pn;
  struct fuse_file_info *info;
};

struct op_release {
  const char *pn;
  struct fuse_file_info *info;
};

struct op_rmdir {
  const char *pn;
};

typedef enum {
  OP_GETATTR = 1,
  OP_MKNOD = 2,
  OP_MKDIR = 3,
  OP_UNLINK = 4,
  OP_OPEN = 5,
  OP_RELEASE = 6,
  OP_RMDIR = 7,
} op_t;

struct operation {
  int op_type;
  int64_t err;
  int done;

  uint64_t t0, t1, t2, t3;

  union {
    struct op_getattr getattr;
    struct op_mknod mknod;
    struct op_mkdir mkdir;
    struct op_unlink unlink;
    struct op_open open;
    struct op_release release;
    struct op_rmdir rmdir;
  } u;
};

void initialize(int num_queues);
struct operation* get_op(int queue_index);
void send_result(struct operation *op, int err);
struct operation* send_result_and_get_op(struct operation *op, int err, int queue_index);
int execute(struct operation *op);

#endif
