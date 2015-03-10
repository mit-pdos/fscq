#define FUSE_USE_VERSION 26
#include <fuse.h>

#include <errno.h>
#include <fcntl.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <sys/types.h>
#include <sys/uio.h>
#include <unistd.h>
#include <time.h>

#define FUSE  1

#include "stat.h"
#include "fs.h"
#include "fcntl.h"

int sys_fstat(const char *path, void *buf);
int sys_read(void *fh, char *buf, size_t sz, off_t off);
int sys_write(char *path, char *buf, size_t sz, off_t off);
void *sys_open(char *path, int omode);
void *sys_create(char *path, int omode);
int sys_fileclose(void *fh);
int sys_readdirent(void *fh, struct dirent *e, off_t off);
int sys_truncate(char *path);
int sys_mkdir(char *path);
int sys_unlink(char *path);
int sys_rename(char *path1, char *path2);
int sys_utime(char *path, int time);
int sys_mksock(char *path);

// Special file for statistics.  cat /stats returns the results and
// resets the counters to 0.
char *stats = "/stats";
struct stats {
  long nread;
  long nwrite;
  long nflush;
  long ngetattr;
  long nopen;
  long nrelease;
  long nreaddir;
  long nfuse_read;
  long nfuse_write;
  long ncreate;
  long ntrunc;
  long nmkdir;
  long nrmdir;
  long nunlink;
} fsstats;
char statsbuf[1024];

void panic(char *s)
{
  printf("PANIC: %s\n", s);
  exit(-1);
}

static int
fuse_getattr(const char *path, struct stat *stbuf)
{
  struct xv6stat st;
  memset(stbuf, 0, sizeof(struct stat));
  memset(&st, 0, sizeof(struct xv6stat));

  if (strcmp(path, stats) == 0) {
    sprintf(statsbuf, "nread %ld\nnwrite %ld\nnflush %ld\nngetattr %ld\nnopen %ld\nnrelease %ld\nnreadir %ld\nnfuse_read %ld\nnfuse_write %ld\nncreate %ld\nntrunc %ld\nnmkdir %ld\nnrmdir %ld\nnunlink %ld\n", fsstats.nread, 
	    fsstats.nwrite, fsstats.nflush, fsstats.ngetattr, fsstats.nopen,
	    fsstats.nrelease, fsstats.nreaddir, fsstats.nfuse_read,
	    fsstats.nfuse_write, fsstats.ncreate, fsstats.ntrunc,
	    fsstats.nmkdir,  fsstats.nrmdir, fsstats.nunlink);
    stbuf->st_mode = S_IFREG | 0444;
    stbuf->st_nlink = 1;
    stbuf->st_size = strlen(statsbuf);
    return 0;
  }
  fsstats.ngetattr++;
  int r = sys_fstat(path, (char *) &st);
  if (r >= 0) {
    stbuf->st_mode = 0777;
    if (st.type == T_DIR)
      stbuf->st_mode |= S_IFDIR;
    else if (st.type == T_SOCK)
      stbuf->st_mode |= S_IFSOCK;
    else
      stbuf->st_mode |= S_IFREG;
    stbuf->st_nlink = st.nlink;
    stbuf->st_size = st.size;
    stbuf->st_atime = st.atime;
    stbuf->st_ctime = st.ctime;
    stbuf->st_mtime = st.mtime;
  } else {
    r = -ENOENT;
  }
  return r;
}

static int
fuse_open(const char *path, struct fuse_file_info *fi)
{
  if (strcmp(path, stats) == 0) {
    return 0;
  }
  fsstats.nopen++;
  void  *r = sys_open((char *) path, fi->flags);
  fi->fh = (uint64_t) r;
  return (r == 0) ? -1 : 0;
}

static int
fuse_release(const char *path, struct fuse_file_info *fi)
{
  if (strcmp(path, stats) == 0) {
    return 0;
  }
  fsstats.nrelease++;
  int r = sys_fileclose((void *) fi->fh);
  return r;
}

static int
fuse_readdir(const char *path, void *buf, fuse_fill_dir_t filler,
	     off_t offset, struct fuse_file_info *fi)
{
  fsstats.nreaddir++;
  void  *fh = sys_open((char *) path, fi->flags);
  if (fh == 0)
    return -1;
  off_t xv6off = 0;
  struct dirent xv6e;
  int r;
  while ((r = sys_readdirent(fh, &xv6e, xv6off)) > 0) {
    xv6off += sizeof(xv6e);
    if(xv6e.inum == 0)
      continue;
    filler(buf, xv6e.name, NULL, 0);
  }
  (void) sys_fileclose(fh);
  return r;
}

static int
fuse_read(const char *path, char *buf, size_t size, off_t offset,
	  struct fuse_file_info *fi)
{
  if (strcmp(path, stats) == 0) {
    int len = strlen(statsbuf);
    if (offset < len) {
      if (offset + size > len)
	size = len - offset;
      memcpy(buf, statsbuf + offset, size);
    } else
      size = 0;
    bzero(&fsstats, sizeof(fsstats));  // reset counters

    return size;
  }
  fsstats.nfuse_read++;
  size = sys_read((char *) fi->fh, buf, size, offset);
  return size;
}

static int
fuse_write(const char *path, const char *buf, size_t size, off_t offset,
	  struct fuse_file_info *fi)
{
  fsstats.nfuse_write++;
  size = sys_write((char *) fi->fh, (char *) buf, size, offset);
  return size;
}

static int
fuse_create(const char *path, mode_t m, struct fuse_file_info *fi)
{
    fsstats.ncreate++;
    int omode = 0;
    if (fi->flags & O_CREAT) {
      omode |= XV6_O_CREATE;
    }
    if (fi->flags & O_RDWR) {
      omode |= XV6_O_RDWR;
    }
    if (fi->flags & O_WRONLY) {
      omode |= XV6_O_WRONLY;
    }
    if (fi->flags & O_RDONLY) {
      omode |= XV6_O_RDONLY;
    }
    void *r = sys_open((char *) path, omode);
    fi->fh = (uint64_t) r;
    return (r == 0) ? -1 : 0;
}

static int
fuse_truncate(const char *path, off_t off)
{
    fsstats.ntrunc++;
    if (off != 0) return -1;
    return sys_truncate((char *) path);
}

static int
fuse_mkdir(const char *path, mode_t m)
{
  fsstats.nmkdir++;
  int r = sys_mkdir((char *)path);
  return r;
}

static int
fuse_rmdir(const char *path)
{
  fsstats.nrmdir++;
  int r = sys_unlink((char *)path);
  return r;
}

static int
fuse_unlink(const char *path)
{
  fsstats.nunlink++;
  int r = sys_unlink((char *)path);
  return r;
}

static int
fuse_rename(const char *path1, const char *path2) {
  return sys_rename((char *) path1, (char *)path2);
}

static int
fuse_utimens(const char *path, const struct timespec tv[2])
{
  return sys_utime((char *) path, tv[2].tv_sec);
}

static int
fuse_chmod(const char *path, mode_t mode)
{
  return 0;
}

static int
fuse_mknod(const char *path, mode_t m, dev_t d)
{
  if (!S_ISSOCK(m))
    return -1;
  return sys_mksock((char*) path);
}

static struct fuse_operations fuse_filesystem_operations = {
  .getattr = fuse_getattr,
  .open    = fuse_open,
  .release = fuse_release,
  .read    = fuse_read,
  .write   = fuse_write,
  .create  = fuse_create,
  .readdir = fuse_readdir,
  .truncate = fuse_truncate,
  .mkdir = fuse_mkdir,
  .unlink = fuse_unlink,
  .rmdir = fuse_rmdir,
  .rename = fuse_rename,
  .utimens = fuse_utimens,
  .chmod = fuse_chmod,
  .mknod = fuse_mknod,
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

void ideinit(char *disk)
{
  if ((fsimg_fd = open(disk, O_RDWR)) < 0) {
    perror("failed to open disk");
    exit(-1);
  }
  printf("xv6fs: opened fs.img\n");
}

void
unix_read(int sector, unsigned char *buf, int sz)
{
  ssize_t n = pread(fsimg_fd, buf, sz, sector*BSIZE);
  if (n != sz) {
    perror("pread failed\n");
    exit(-1);
  }
  fsstats.nread++;
}

void
unix_write(int sector, unsigned char *buf, int sz)
{
  ssize_t n = pwrite(fsimg_fd, buf, sz, sector*BSIZE);
  if (n != sz) {
    perror("pwrite failed\n");
    exit(-1);
  }
  fsstats.nwrite++;
}

void
unix_flush(void) 
{
  int r = fsync(fsimg_fd);
  if (r != 0) {
    perror("fsync failed\n");
    exit(-1);
  }
  fsstats.nflush++;
}

int 
unix_time(void) {
  time_t t;
  t = time(0);
  return (int) t;
}

void binit();
void fileinit();
void initlog();

int
main(int argc, char **argv)
{
  
  if (argc < 2) {
    printf("%s disk-file fuse-args\n", argv[0]);
    exit(1);
  }
  printf("init xv6\n");
  binit();
  fileinit();
  ideinit(argv[1]);
  initlog();
  printf("init xv6 done\n");
  int i;
  for (i = 2; i < argc; i++) {
    argv[i-1] = argv[i];
  }
  argc--;
  return fuse_main(argc, argv, &fuse_filesystem_operations, NULL);
}
