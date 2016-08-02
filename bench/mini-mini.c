#define _GNU_SOURCE 1
#include <stdio.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>

int
main(int ac, char **av)
{
  int fd = open("test.one", O_CREAT | O_EXCL | O_WRONLY, 0666);
  close(fd);

  int dfd = open(".", O_RDONLY | O_DIRECTORY);

  for (int i = 0; i < 100; i++) {
    rename("test.one", "test.two");
    fsync(dfd);

    rename("test.two", "test.one");
    fsync(dfd);
  }

  unlink("test.one");
}
