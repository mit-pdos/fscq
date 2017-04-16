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
#include <fcntl.h>
#include <sys/stat.h>
#include <dirent.h>
#include <errno.h>
#include <sys/time.h>
#ifdef HAVE_SETXATTR
#include <sys/xattr.h>
#endif
#include "opqueue.h"

static int opfuse_getattr(const char *path, struct stat *stbuf)
{
  struct operation op;

  op.op_type = OP_GETATTR;
  op.u.getattr.pn = path;
  op.u.getattr.st = stbuf;
  execute(&op);
  return op.err;
}

#if 0
static int opfuse_readdir(const char *path, void *buf, fuse_fill_dir_t filler,
		       off_t offset, struct fuse_file_info *fi)
{
	DIR *dp;
	struct dirent *de;

	(void) offset;
	(void) fi;

	dp = opendir(path);
	if (dp == NULL)
		return -errno;

	while ((de = readdir(dp)) != NULL) {
		struct stat st;
		memset(&st, 0, sizeof(st));
		st.st_ino = de->d_ino;
		st.st_mode = de->d_type << 12;
		if (filler(buf, de->d_name, &st, 0))
			break;
	}

	closedir(dp);
	return 0;
}
#endif

static int opfuse_mknod(const char *path, mode_t mode, dev_t rdev)
{
  struct operation op;

  op.op_type = OP_MKNOD;
  op.u.mknod.pn = path;
  op.u.mknod.mode = mode;
  op.u.mknod.rdev = rdev;
  execute(&op);
  return op.err;
}

static int opfuse_mkdir(const char *path, mode_t mode)
{
  struct operation op;

  op.op_type = OP_MKDIR;
  op.u.mkdir.pn = path;
  op.u.mkdir.mode = mode;
  execute(&op);
  return op.err;
}

static int opfuse_unlink(const char *path)
{
  struct operation op;

  op.op_type = OP_UNLINK;
  op.u.unlink.pn = path;
  execute(&op);
  return op.err;
}

#if 0
static int opfuse_rmdir(const char *path)
{
	int res;

	res = rmdir(path);
	if (res == -1)
		return -errno;

	return 0;
}

static int opfuse_symlink(const char *from, const char *to)
{
	int res;

	res = symlink(from, to);
	if (res == -1)
		return -errno;

	return 0;
}

static int opfuse_rename(const char *from, const char *to)
{
	int res;

	res = rename(from, to);
	if (res == -1)
		return -errno;

	return 0;
}

static int opfuse_link(const char *from, const char *to)
{
	int res;

	res = link(from, to);
	if (res == -1)
		return -errno;

	return 0;
}

static int opfuse_chmod(const char *path, mode_t mode)
{
	int res;

	res = chmod(path, mode);
	if (res == -1)
		return -errno;

	return 0;
}

static int opfuse_chown(const char *path, uid_t uid, gid_t gid)
{
	int res;

	res = lchown(path, uid, gid);
	if (res == -1)
		return -errno;

	return 0;
}

static int opfuse_truncate(const char *path, off_t size)
{
	int res;

	res = truncate(path, size);
	if (res == -1)
		return -errno;

	return 0;
}

static int opfuse_open(const char *path, struct fuse_file_info *fi)
{
	int res;

	res = open(path, fi->flags);
	if (res == -1)
		return -errno;

	close(res);
	return 0;
}

static int opfuse_read(const char *path, char *buf, size_t size, off_t offset,
		    struct fuse_file_info *fi)
{
	int fd;
	int res;

	(void) fi;
	fd = open(path, O_RDONLY);
	if (fd == -1)
		return -errno;

	res = pread(fd, buf, size, offset);
	if (res == -1)
		res = -errno;

	close(fd);
	return res;
}

static int opfuse_write(const char *path, const char *buf, size_t size,
		     off_t offset, struct fuse_file_info *fi)
{
	int fd;
	int res;

	(void) fi;
	fd = open(path, O_WRONLY);
	if (fd == -1)
		return -errno;

	res = pwrite(fd, buf, size, offset);
	if (res == -1)
		res = -errno;

	close(fd);
	return res;
}

static int opfuse_statfs(const char *path, struct statvfs *stbuf)
{
	int res;

	res = statvfs(path, stbuf);
	if (res == -1)
		return -errno;

	return 0;
}

static int opfuse_release(const char *path, struct fuse_file_info *fi)
{
	/* Just a stub.	 This method is optional and can safely be left
	   unimplemented */

	(void) path;
	(void) fi;
	return 0;
}

static int opfuse_fsync(const char *path, int isdatasync,
		     struct fuse_file_info *fi)
{
	/* Just a stub.	 This method is optional and can safely be left
	   unimplemented */

	(void) path;
	(void) isdatasync;
	(void) fi;
	return 0;
}
#endif

static struct fuse_operations opfuse_oper = {
	.getattr	= opfuse_getattr,
	// .readdir	= opfuse_readdir,
	.mknod		= opfuse_mknod,
	.mkdir		= opfuse_mkdir,
	.unlink		= opfuse_unlink,
	// .rmdir		= opfuse_rmdir,
	// .rename		= opfuse_rename,
	// .chmod		= opfuse_chmod,
	// .chown		= opfuse_chown,
	// .truncate	= opfuse_truncate,
	// .open		= opfuse_open,
	// .read		= opfuse_read,
	// .write		= opfuse_write,
	// .statfs		= opfuse_statfs,
	// .release	= opfuse_release,
	// .fsync		= opfuse_fsync,
};

int main(int argc, char *argv[])
{
  umask(0);
  return fuse_main(argc, argv, &opfuse_oper, NULL);
}
