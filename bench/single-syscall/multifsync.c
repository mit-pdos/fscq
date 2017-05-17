#include <stdio.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

int
main(int ac, char** av)
{
  int fd = open(av[1], O_RDWR | O_CREAT, 0666);
  if (fd < 0)
    perror("open");

  for (int i = 0; i < 100000; i++) {
    char buf[4096];
    pwrite(fd, buf, 4096, 0);

    fsync(fd);
  }
}
