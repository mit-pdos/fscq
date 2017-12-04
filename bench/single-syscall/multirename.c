#include <stdio.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

int
main(int ac, char** av)
{
  char* base = av[1];

  char d1[128];
  char d2[128];

  sprintf(d1, "%s/d1", base);
  sprintf(d2, "%s/d2", base);
  mkdir(d1);
  mkdir(d2);

  for (int i = 0; i < 1000; i++) {
    int fd = open(fn, O_CREAT | O_RDWR | O_EXCL, 0666);
    if (fd < 0)
      perror("open");

    close(fd);

    unlink(fn);
  }
}
