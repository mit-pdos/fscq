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

void printstats(char *fs, int reset)
{
  int fd;
  int r;

  sprintf(name, "%s/stats", fs);
  if((fd = open(name, O_RDONLY)) < 0) {
    perror("open stats");
    return;
  }

  bzero(buf, BUFSIZE);

  if ((r = read(fd, buf, BUFSIZE)) < 0) {
    perror("read");
    exit(1);
  }

  if (!reset) fprintf(stdout, "=== FS Stats ===\n%s========\n", buf);

  if ((r = close(fd)) < 0) {
    perror("close");
  }
}
