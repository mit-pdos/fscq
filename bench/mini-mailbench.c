#define _GNU_SOURCE 1
#include <stdio.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>

static void
xerror(char *msg)
{
  perror(msg);
  exit(-1);
}

int
main(int ac, char **av)
{
  char msg[64];
  snprintf(msg, sizeof(msg), "Hello world!\n");
  size_t msglen = strlen(msg);

  for (int i = 0; i < 300; i++) {
    char tmp1[64];
    snprintf(tmp1, sizeof(tmp1), "tmp.%d.1", i);

    char tmp2[64];
    snprintf(tmp2, sizeof(tmp2), "tmp.%d.2", i);

    char fn1[64];
    snprintf(fn1, sizeof(fn1), "q.%d.1", i);

    char fn2[64];
    snprintf(fn2, sizeof(fn2), "q.%d.2", i);

    int fd1 = open(tmp1, O_CREAT | O_EXCL | O_WRONLY, 0666);
    if (fd1 < 0)
      xerror("open1");

    write(fd1, msg, msglen);
    fdatasync(fd1);
    close(fd1);

    int fd2 = open(tmp2, O_CREAT | O_EXCL | O_WRONLY, 0666);
    if (fd2 < 0)
      xerror("open2");

    write(fd2, msg, msglen);
    fdatasync(fd2);
    close(fd2);

    if (rename(tmp1, fn1) < 0)
      xerror("rename1");

    int dirfd1 = open(".", O_RDONLY | O_DIRECTORY);
    if (dirfd1 < 0)
      xerror("opendir1");
    fsync(dirfd1);
    close(dirfd1);

    if (rename(tmp2, fn2) < 0)
      xerror("rename2");

    int dirfd2 = open(".", O_RDONLY | O_DIRECTORY);
    if (dirfd2 < 0)
      xerror("opendir2");
    fsync(dirfd2);
    close(dirfd2);
  }
}
