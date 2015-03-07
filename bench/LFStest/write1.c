#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <errno.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <strings.h>
#include "stats.h"

#define BUFSIZE 1024
char buf[BUFSIZE];
char name[BUFSIZE];

#define NITER 100
#define DOSTATS 0

int main(int argc, char **argv)
{
  int fd;
  int r;
  int i;
  int iter;

  sprintf(name, "%s/write1", argv[1]);

  for (iter = 0; iter < NITER; iter++) {

    if((fd = open(name, O_CREAT | O_TRUNC | O_RDWR, 0666)) < 0) {
      perror("open");
      exit(1);
    }

#if DOSTATS
    printstats(argv[1], 1);
#endif

    for (i = 0; i < BUFSIZE; i++) buf[i] = 'a';

    if ((r = write(fd, buf, BUFSIZE)) < 0) {
      perror("write");
      exit(1);
    }

#if DOSTATS
    printstats(argv[1], 0);
#endif

    if ((r = close(fd)) < 0) {
      perror("close");
    }

    if ((r = unlink(name)) < 0) {
      perror("unlink");
    }

  }

  return 0;
}
