#include "types.h"
#include "defs.h"
#include "param.h"
#include "stat.h"
#include "fs.h"
#include "file.h"
#include "fcntl.h"

#include <string.h>

static struct inode*
create(char *path, short type, short major, short minor)
{
  uint off;
  struct inode *ip, *dp;
  char name[DIRSIZ];

  if((dp = nameiparent(path, name)) == 0)
    return 0;

  ilock(dp);
  
  if((ip = dirlookup(dp, name, &off)) != 0){
    iunlockput(dp);
    ilock(ip);
    if(type == T_FILE && ip->type == T_FILE)
      return ip;
    iunlockput(ip);
    return 0;
  }

  if((ip = ialloc(dp->dev, type)) == 0)
    panic("create: ialloc");

  ilock(ip);
  ip->major = major;
  ip->minor = minor;
  ip->nlink = 1;
  ip->atime = ip->mtime = ip->ctime = unix_time();
  iupdate(ip);

  if(type == T_DIR){  // Create . and .. entries.
    dp->nlink++;  // for ".."
    iupdate(dp);
    // No ip->nlink++ for ".": avoid cyclic ref count.
    if(dirlink(ip, ".", ip->inum) < 0 || dirlink(ip, "..", dp->inum) < 0)
      panic("create dots");
  }

  if(dirlink(dp, name, ip->inum) < 0)
    panic("create: dirlink");

  iunlockput(dp);

  return ip;
}

struct file*
sys_open(char *path, int omode)
{
  struct file *f;
  struct inode *ip;

  begin_op();

  if(omode & O_CREATE){
    ip = create(path, T_FILE, 0, 0);
    if(ip == 0){
      end_op();
      return 0;
    }
  } else {
    if((ip = namei(path)) == 0){
      end_op();
      return 0;
    }
    ilock(ip);
    if(ip->type == T_DIR && omode != O_RDONLY){
      iunlockput(ip);
      end_op();
      return 0;
    }
  }

  if((f = filealloc()) == 0) {
    if(f)
      fileclose(f);
    iunlockput(ip);
    end_op();
    return 0;
  }
  iunlock(ip);
  end_op();

  f->type = FD_INODE;
  f->ip = ip;
  f->off = 0;
  f->readable = !(omode & O_WRONLY);
  f->writable = (omode & O_WRONLY) || (omode & O_RDWR);
  return f;
}

int
sys_fileclose(void *fh)
{
  struct file *f = (struct file *) fh;
  fileclose(f);
  return 0;
}


int
sys_read(void *fh, char *buf, size_t sz, uint off)
{
  struct file *f = (struct file *) fh;
  if (f == 0)
    return -1;
  f->off = off;
  return fileread(f, buf, sz);
}

int
sys_write(void *fh, char *buf, size_t sz, uint off)
{
  struct file *f = (struct file *) fh;
  if (f == 0)
    return -1;
  f->off = off;
  int r = filewrite(f, buf, sz);
  // cprintf("write %d sz at off %d -> %d\n", sz, off, r);
  return r;
}


int
sys_fstat(char *path, void *buf)
{
  struct file *f = sys_open(path, O_RDONLY);
  if (f == 0)
    return -1;
  int r = filestat(f, (struct stat *)buf);
  fileclose(f);
  return r;
}

int
sys_readdirent(void *fh, struct dirent *e, uint off)
{
  struct file *f = (struct file *) fh;
  if ((f == 0) || (f->ip->type != T_DIR))
    return -1;
  if (off >= f->ip->size)
    return 0;
  f->off = off;
  int r = fileread(f, (char *) e, sizeof(*e));
  return r;
}

int
sys_truncate(char *path) {
  struct file *f = sys_open(path, O_RDWR);
  if (f == 0) return -1;
  begin_op();
  itrunc(f->ip);
  end_op();
  fileclose(f);
  return 0;
}

int 
sys_mkdir(char *path) {
  struct inode *ip;

  begin_op();
  if((ip = create(path, T_DIR, 0, 0)) == 0){
    end_op();
    return -1;
  }
  iunlockput(ip);
  end_op();
  return 0;
}

int
sys_mksock(char *path) {
  struct inode *ip;

  begin_op();
  if((ip = create(path, T_SOCK, 0, 0)) == 0){
    end_op();
    return -1;
  }
  iunlockput(ip);
  end_op();
  return 0;
}

// Is the directory dp empty except for "." and ".." ?
static int
isdirempty(struct inode *dp)
{
  int off;
  struct dirent de;

  for(off=2*sizeof(de); off<dp->size; off+=sizeof(de)){
    if(readi(dp, (char*)&de, off, sizeof(de)) != sizeof(de))
      panic("isdirempty: readi");
    if(de.inum != 0)
      return 0;
  }
  return 1;
}

#define ENOENT (-2)

int
sys_dounlink(char *path)
{
  struct inode *ip, *dp;
  struct dirent de;
  char name[DIRSIZ];
  uint off;
  int r = -1;

  if((dp = nameiparent(path, name)) == 0){
    return -1;
  }

  ilock(dp);

  // Cannot unlink "." or "..".
  if(namecmp(name, ".") == 0 || namecmp(name, "..") == 0)
    goto bad;

  if((ip = dirlookup(dp, name, &off)) == 0) {
    r = ENOENT;
    goto bad;
  }

  ilock(ip);

  if(ip->nlink < 1)
    panic("unlink: nlink < 1");

  if(ip->type == T_DIR && !isdirempty(ip)){
    iunlockput(ip);
    goto bad;
  }

  memset(&de, 0, sizeof(de));
  if(writei(dp, (char*)&de, off, sizeof(de)) != sizeof(de))
    panic("unlink: writei");
  if(ip->type == T_DIR){
    dp->nlink--;
    iupdate(dp);
  }
  iunlockput(dp);

  ip->nlink--;
  iupdate(ip);
  iunlockput(ip);

  return 0;

bad:
  iunlockput(dp);
  return r;
}

int
sys_unlink(char *path)
{
  int r;
  begin_op();
  r = sys_dounlink(path);
  end_op();
  return r;
}

// Create the path new as a link to the same inode as old.
int
sys_dolink(char *old, char *new)
{
  struct inode *dp, *ip;
  char name[DIRSIZ];

  if((ip = namei(old)) == 0){
    end_op();
    return -1;
  }

  ilock(ip);
  if(ip->type == T_DIR){
    iunlockput(ip);
    end_op();
    return -1;
  }

  ip->nlink++;
  iupdate(ip);
  iunlock(ip);

  if((dp = nameiparent(new, name)) == 0)
    goto bad;
  ilock(dp);
  if(dp->dev != ip->dev || dirlink(dp, name, ip->inum) < 0){
    iunlockput(dp);
    goto bad;
  }
  iunlockput(dp);
  iput(ip);

  return 0;

bad:
  ilock(ip);
  ip->nlink--;
  iupdate(ip);
  iunlockput(ip);
  return -1;
}

int
sys_rename(char *path1, char *path2)
{
  int r = -1;

  begin_op();
  r = sys_dounlink(path2);
  if ((r == 0) || (r == ENOENT)) {
    r = sys_dolink(path1, path2);
    if (r == 0) {
      r = sys_dounlink(path1);
    }
  }
  end_op();
  return r;
}

int 
sys_utime(char *path, int time)
{
  struct file *f = sys_open(path, O_WRONLY);
  if (f == 0)
    return -1;
  begin_op();
  ilock(f->ip);
  f->ip->mtime = time;
  iupdate(f->ip);
  iunlock(f->ip);
  end_op();
  fileclose(f);
  return 0;
}

/*
int
sys_chdir(void)
{
  char *path;
  struct inode *ip;

  begin_op();
  if(argstr(0, &path) < 0 || (ip = namei(path)) == 0){
    end_op();
    return -1;
  }
  ilock(ip);
  if(ip->type != T_DIR){
    iunlockput(ip);
    end_op();
    return -1;
  }
  iunlock(ip);
  iput(proc->cwd);
  end_op();
  proc->cwd = ip;
  return 0;
}

*/
