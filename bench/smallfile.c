#include <stdio.h>
#include <errno.h>
#include <fcntl.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <stdint.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/time.h>

#define N 1000
#define FILESIZE 100
#define NAMESIZE 100

static char name[NAMESIZE];
static char buf[FILESIZE]; 

static uint64_t
usec_now()
{
  struct timeval tv;

  gettimeofday(&tv, NULL);

  uint64_t res = tv.tv_sec;
  res *= 1000000;
  res += tv.tv_usec;
  return res;
}

int main(int argc, char *argv[])
{
  int i;
  int r;
  int fd;
  uint64_t start, end;

  sprintf(buf, "%s/d", argv[1]);
  if (mkdir(buf,  S_IRWXU) < 0) {
    printf("%s: create %s failed %s\n", argv[0], buf, strerror(errno));
    exit(1);
  }
  start = usec_now();
  for (i = 0; ; i++) {
    sprintf(name, "%s/d/f%d", argv[1], i);
    if((fd = open(name, O_RDWR | O_CREAT | O_TRUNC, S_IRWXU)) < 0) {
      printf("%s: create %s failed %s\n", argv[0], name, strerror(errno));
      exit(1);
    }
    if (write(fd, buf, FILESIZE) != FILESIZE) {
      printf("%s: write %s failed %s\n", argv[0], name, strerror(errno));
      exit(1);
    }
    if (fsync(fd) < 0) {
      printf("%s: fsync %s failed %s\n", argv[0], name, strerror(errno));
      exit(1);
    }
    close(fd);

    end = usec_now();
    if (end - start > 1000000)
      break;
  }

  printf("%d files per %ld usec\n", i, end-start);
}
