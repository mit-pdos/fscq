#define _GNU_SOURCE 1
#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <fcntl.h>
#include <string.h>

int
main(int ac, char **av)
{
  char *msg = "hello\n";
  int fd = open("temp", O_CREAT | O_RDWR, 0666);
  if (fd < 0) {
    perror("open temp");
    exit(-1);
  }

  size_t cc = strlen(msg);
  if (write(fd, msg, cc) != cc) {
    perror("write");
    exit(-1);
  }

  if (fdatasync(fd) < 0) {
    perror("fdatasync");
    exit(-1);
  }

  close(fd);

  if (rename("temp", "dst") < 0) {
    perror("rename");
    exit(-1);
  }

  fd = open(".", O_DIRECTORY | O_RDONLY);
  if (fd < 0) {
    perror("open dir");
    exit(-1);
  }

  if (fsync(fd) < 0) {
    perror("fsync");
    exit(-1);
  }
}
