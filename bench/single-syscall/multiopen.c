#include <stdio.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

int
main(int ac, char** av)
{
  for (int i = 0; i < 100000; i++) {
    int fd = open(av[1], O_RDONLY);
    if (fd >= 0)
      close(fd);
  }
}
