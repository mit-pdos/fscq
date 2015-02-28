#include <errno.h>
#include <fcntl.h>
#include <string.h>
#include <fuse.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <sys/types.h>
#include <sys/uio.h>
#include <unistd.h>

//
// XXX use file handle instead of pathname for read/write
// XXX deal with offset in read/write (implement seek in xv6?)
// XXX modes
//

#define FUSE

#include "stat.h"

int sys_fstat(const char *path, void *buf);
int sys_read(char *path, char *buf, size_t sz, off_t off);
int sys_write(char *path, char *buf, size_t sz, off_t off);
void *sys_open(char *path, int omode);
void *sys_create(char *path, int omode);

static int
fuse_getattr(const char *path, struct stat *stbuf)
{
  struct xv6stat st;
  memset(stbuf, 0, sizeof(struct stat));
  memset(&st, 0, sizeof(struct xv6stat));

  printf("fuse_getattr: %s\n", path);

  int r = sys_fstat(path, (char *) &st);
  printf("sys_fstat: %d %d %d %d\n", r, st.type, st.nlink, st.size);
  if (r >= 0) {
    stbuf->st_mode = (st.type == T_DIR) ? S_IFDIR | 0777 : S_IFREG | 0666;
    stbuf->st_nlink = st.nlink;
    stbuf->st_size = st.size;
  } else {
    r = -ENOENT;
  }
  return r;
}

static int
fuse_open(const char *path, struct fuse_file_info *fi)
{
  printf("fuse_open: %s flags %d\n", path, fi->flags);
  void  *r = sys_open((char *) path, 1);
  return (r == 0) ? -1 : 0;
}

static int
fuse_readdir(const char *path, void *buf, fuse_fill_dir_t filler,
	     off_t offset, struct fuse_file_info *fi)
{
  printf("fuse_readir: %s\n", path);
      
  return -ENOENT;
}

static int
fuse_read(const char *path, char *buf, size_t size, off_t offset,
	  struct fuse_file_info *fi)
{
  printf("fuse_read: %s %ld %lld\n", path, size, offset);
  size = sys_read((char *) path, buf, size, offset);
  return size;
}

static int
fuse_write(const char *path, const char *buf, size_t size, off_t offset,
	  struct fuse_file_info *fi)
{
  printf("fuse_read: %s %ld %lld\n", path, size, offset);
  size = sys_write((char *) path, (char *) buf, size, offset);
  return size;
}

static int
fuse_create(const char *path, mode_t m, struct fuse_file_info *fi)
{
    printf("fuse_create: %s %x\n", path, m);
    void *r = sys_open((char *) path, 0x200);  /* O_CREATE */
    return (r == 0) ? -1 : 0;
}

static struct fuse_operations fuse_filesystem_operations = {
  .getattr = fuse_getattr, /* To provide size, permissions, etc. */
  .open    = fuse_open,    /* To enforce read-only access.       */
  .read    = fuse_read,    /* To provide file content.           */
  .write   = fuse_write,   /* To write file content.             */
  .create  = fuse_create,  /* To create a file.                  */
  .readdir = fuse_readdir, /* To provide directory listing.      */
};

void
cprintf(char *fmt, ...)
{
  va_list argptr;
  va_start(argptr, fmt);
  vprintf(fmt, argptr);
  va_end(argptr);
}

static int fsimg_fd;

void ideinit()
{
  if ((fsimg_fd = open("fs.img", O_RDWR)) < 0) {
    perror("failed to open fs.img");
    exit(-1);
  }
  printf("xv6fs: opened fs.img\n");
}

void
unix_read(int sector, unsigned char *buf, int sz)
{
  ssize_t n = pread(fsimg_fd, buf, sz, sector*512);
  if (n != sz) {
    perror("pread failed\n");
    exit(-1);
  }
}

void
unix_write(int sector, unsigned char *buf, int sz)
{
  ssize_t n = pwrite(fsimg_fd, buf, sz, sector*512);
  if (n != sz) {
    perror("pwrite failed\n");
    exit(-1);
  }
}

void binit();
void fileinit();
void initlog();

int
main(int argc, char **argv)
{
  printf("init xv6\n");
  binit();
  fileinit();
  ideinit();
  initlog();
  printf("init xv6 done\n");
  return fuse_main(argc, argv, &fuse_filesystem_operations, NULL);
}
