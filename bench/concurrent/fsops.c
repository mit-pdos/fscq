#include <fcntl.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

int main(int argc, char *argv[]) {
  if (argc < 4) {
    fprintf(stderr, "Usage: fsops <stat|open> <path> <kiters>\n");
    return 1;
  }
  char *op = argv[1];
  char *path = argv[2];
  char *kiters_s = argv[3];

  int iters = atoi(kiters_s) * 1000;
  if (iters <= 0) {
    fprintf(stderr, "kiters should be above 0\n");
    return 1;
  }

  if (strcmp(op, "stat") == 0) {
    struct stat buf;
    for (int i = 0; i < iters; i++) {
      stat(path, &buf);
    }
    return 0;
  }
  if (strcmp(op, "open") == 0) {
    for (int i = 0; i < iters; i++) {
      int fd = open(path, O_RDONLY);
      if (fd > 0) {
        close(fd);
      }
    }
    return 0;
  }
  return 1;
}
