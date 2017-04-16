#define FUSE_USE_VERSION 26

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#ifdef linux
/* For pread()/pwrite()/utimensat() */
#define _XOPEN_SOURCE 700
#endif

#include <fuse.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <stdlib.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <dirent.h>
#include <errno.h>
#include <sys/time.h>
#include "opqueue.h"

static int
opfuse_getattr(const char *path, struct stat *stbuf)
{
  struct operation op;

  op.op_type = OP_GETATTR;
  op.u.getattr.pn = path;
  op.u.getattr.st = stbuf;
  execute(&op);
  return op.err;
}

static int
opfuse_mknod(const char *path, mode_t mode, dev_t rdev)
{
  struct operation op;

  op.op_type = OP_MKNOD;
  op.u.mknod.pn = path;
  op.u.mknod.mode = mode;
  op.u.mknod.rdev = rdev;
  execute(&op);
  return op.err;
}

static int
opfuse_mkdir(const char *path, mode_t mode)
{
  struct operation op;

  op.op_type = OP_MKDIR;
  op.u.mkdir.pn = path;
  op.u.mkdir.mode = mode;
  execute(&op);
  return op.err;
}

static int
opfuse_unlink(const char *path)
{
  struct operation op;

  op.op_type = OP_UNLINK;
  op.u.unlink.pn = path;
  execute(&op);
  return op.err;
}

static int
opfuse_rmdir(const char *path)
{
  struct operation op;

  op.op_type = OP_RMDIR;
  op.u.rmdir.pn = path;
  execute(&op);
  return op.err;
}

static int
opfuse_open(const char *path, struct fuse_file_info *fi)
{
  struct operation op;

  op.op_type = OP_OPEN;
  op.u.open.pn = path;
  op.u.open.info = fi;
  execute(&op);
  return op.err;
}

static int
opfuse_release(const char *path, struct fuse_file_info *fi)
{
  struct operation op;

  op.op_type = OP_RELEASE;
  op.u.release.pn = path;
  op.u.release.info = fi;
  execute(&op);
  return op.err;
}

static int
opfuse_read(const char *path, char *buf, size_t size, off_t offset,
	    struct fuse_file_info *fi)
{
  struct operation op;

  op.op_type = OP_READ;
  op.u.read.pn = path;
  op.u.read.buf = buf;
  op.u.read.bufsiz = size;
  op.u.read.off = offset;
  op.u.read.info = fi;
  execute(&op);
  return op.err;
}

static int
opfuse_write(const char *path, const char *buf, size_t size,
	     off_t offset, struct fuse_file_info *fi)
{
  struct operation op;

  op.op_type = OP_WRITE;
  op.u.write.pn = path;
  op.u.write.buf = buf;
  op.u.write.bufsiz = size;
  op.u.write.off = offset;
  op.u.write.info = fi;
  execute(&op);
  return op.err;
}

static int
opfuse_fsync(const char *path, int isdatasync,
	     struct fuse_file_info *fi)
{
  struct operation op;

  op.op_type = OP_FSYNC;
  op.u.fsync.pn = path;
  op.u.fsync.isdatasync = isdatasync;
  op.u.fsync.info = fi;
  execute(&op);
  return op.err;
}

static int
opfuse_fsyncdir(const char *path, int isdatasync,
	        struct fuse_file_info *fi)
{
  struct operation op;

  op.op_type = OP_FSYNCDIR;
  op.u.fsyncdir.pn = path;
  op.u.fsyncdir.isdatasync = isdatasync;
  op.u.fsyncdir.info = fi;
  execute(&op);
  return op.err;
}

static int
opfuse_truncate(const char *path, off_t size)
{
  struct operation op;

  op.op_type = OP_TRUNCATE;
  op.u.truncate.pn = path;
  op.u.truncate.size = size;
  execute(&op);
  return op.err;
}

static int
opfuse_rename(const char *from, const char *to)
{
  struct operation op;

  op.op_type = OP_RENAME;
  op.u.rename.src = from;
  op.u.rename.dst = to;
  execute(&op);
  return op.err;
}

static int
opfuse_chmod(const char *path, mode_t mode)
{
  struct operation op;

  op.op_type = OP_CHMOD;
  op.u.chmod.pn = path;
  op.u.chmod.mode = mode;
  execute(&op);
  return op.err;
}

static int
opfuse_statfs(const char *path, struct statvfs *stbuf)
{
  struct operation op;

  op.op_type = OP_STATFS;
  op.u.statfs.pn = path;
  op.u.statfs.st = stbuf;
  execute(&op);
  return op.err;
}

static int
opfuse_opendir(const char *path, struct fuse_file_info *fi)
{
  struct operation op;

  op.op_type = OP_OPENDIR;
  op.u.opendir.pn = path;
  op.u.opendir.info = fi;
  execute(&op);
  return op.err;
}

static int
opfuse_readdir(const char *path, void *buf, fuse_fill_dir_t filler,
	       off_t offset, struct fuse_file_info *fi)
{
  struct operation op;

  op.op_type = OP_READDIR;
  op.u.readdir.pn = path;
  op.u.readdir.buf = buf;
  op.u.readdir.fill = filler;
  op.u.readdir.off = offset;
  op.u.readdir.info = fi;
  execute(&op);
  return op.err;
}

static int
opfuse_releasedir(const char *path, struct fuse_file_info *fi)
{
  struct operation op;

  op.op_type = OP_RELEASEDIR;
  op.u.releasedir.pn = path;
  op.u.releasedir.info = fi;
  execute(&op);
  return op.err;
}

static int
opfuse_utime(const char *path, struct utimbuf *buf)
{
  struct operation op;

  op.op_type = OP_UTIME;
  op.u.utime.pn = path;
  op.u.utime.buf = buf;
  execute(&op);
  return op.err;
}

static void
opfuse_destroy(void *arg)
{
  struct operation op;

  op.op_type = OP_DESTROY;
  execute(&op);
}

static struct fuse_operations opfuse_oper = {
	.getattr	= opfuse_getattr,
	.mknod		= opfuse_mknod,
	.mkdir		= opfuse_mkdir,
	.unlink		= opfuse_unlink,
	.rmdir		= opfuse_rmdir,
	.open		= opfuse_open,
	.release	= opfuse_release,
	.read		= opfuse_read,
	.write		= opfuse_write,
	.fsync		= opfuse_fsync,
	.rename		= opfuse_rename,
	.chmod		= opfuse_chmod,
	.truncate	= opfuse_truncate,
	.statfs		= opfuse_statfs,
	.opendir	= opfuse_opendir,
	.readdir	= opfuse_readdir,
	.releasedir	= opfuse_releasedir,
	.fsyncdir	= opfuse_fsyncdir,
        .utime          = opfuse_utime,
        .destroy        = opfuse_destroy,
};

void
opfuse_run(const char *mountpoint, struct fuse_args *args)
{
  struct fuse_chan *chan = fuse_mount(mountpoint, args);
  if (!chan) {
    fprintf(stderr, "fuse_mount\n");
    exit(-1);
  }

  if (chdir("/") < 0) {
    perror("chdir /");
    exit(-1);
  }

  umask(0);

  struct fuse *f = fuse_new(chan, args, &opfuse_oper, sizeof(opfuse_oper), NULL);
  if (!f) {
    fprintf(stderr, "fuse_new\n");
    exit(-1);
  }

  fuse_loop_mt(f);
}
