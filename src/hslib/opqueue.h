#define FUSE_USE_VERSION 26
#ifndef OPQUEUE_H
#define OPQUEUE_H
#include <sys/stat.h>
#include <pthread.h>
#include <inttypes.h>
#include <fuse.h>

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

struct op_truncate {
  const char *pn;
  off_t size;
};

struct op_opendir {
  const char *pn;
  struct fuse_file_info *info;
};

struct op_readdir {
  const char *pn;
  void *buf;
  fuse_fill_dir_t fill;
  off_t off;
  struct fuse_file_info *info;
};

struct op_releasedir {
  const char *pn;
  struct fuse_file_info *info;
};

struct op_statfs {
  const char *pn;
  struct statvfs *st;
};

struct op_destroy {
};

struct op_utime {
  const char *pn;
  struct utimbuf *buf;
};

struct op_rename {
  const char *src;
  const char *dst;
};

struct op_chmod {
  const char *pn;
  mode_t mode;
};

struct op_create {
  const char *pn;
  mode_t mode;
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
  OP_TRUNCATE,
  OP_OPENDIR,
  OP_READDIR,
  OP_RELEASEDIR,
  OP_STATFS,
  OP_DESTROY,
  OP_UTIME,
  OP_RENAME,
  OP_CHMOD,
  OP_CREATE,
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
    struct op_truncate truncate;
    struct op_opendir opendir;
    struct op_readdir readdir;
    struct op_releasedir releasedir;
    struct op_statfs statfs;
    struct op_destroy destroy;
    struct op_utime utime;
    struct op_rename rename;
    struct op_chmod chmod;
    struct op_create create;
  } u;
};

void initialize(int n);
struct operation* get_op(int qi);
void send_result(struct operation *op, int err);
int execute(struct operation *op);
void print_opqueue_timings();

#endif
