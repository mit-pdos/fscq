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

struct op_fsync {
  const char *pn;
  int isdatasync;
  struct fuse_file_info *info;
};

struct op_fsyncdir {
  const char *pn;
  int isdatasync;
  struct fuse_file_info *info;
};

struct op_write {
  const char *pn;
  const char *buf;
  size_t bufsiz;
  off_t off;
  struct fuse_file_info *info;
};

struct op_read {
  const char *pn;
  char *buf;
  size_t bufsiz;
  off_t off;
  struct fuse_file_info *info;
};

typedef enum {
  OP_GETATTR,
  OP_MKNOD,
  OP_MKDIR,
  OP_UNLINK,
  OP_OPEN,
  OP_RELEASE,
  OP_RMDIR,
  OP_FSYNC,
  OP_FSYNCDIR,
  OP_WRITE,
  OP_READ,
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
    struct op_fsync fsync;
    struct op_fsyncdir fsyncdir;
    struct op_write write;
    struct op_read read;
  } u;
};

void initialize();
struct operation* get_op();
void send_result(struct operation *op, int err);
struct operation* send_result_and_get_op(struct operation *op, int err);
int execute(struct operation *op);

#endif
