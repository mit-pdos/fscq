#include <stdio.h>
#include <fcntl.h>
#include <unistd.h>

static const int niter = 1000;

int
main(int ac, char **av)
{
  if (ac != 4) {
    printf("Usage: %s dir dir/f1 dir/f2\n", av[0]);
    return 1;
  }

  const char* dir = av[1];
  const char* f1 = av[2];
  const char* f2 = av[3];

  int dir_fd = open(dir, O_RDONLY | O_DIRECTORY);
  if (dir_fd < 0) {
    perror("open");
    return 1;
  }

  for (int i = 0; i < niter; i++) {
    int fd = open(f1, O_RDWR | O_CREAT | O_EXCL, 0666);
    if (fd < 0) {
      perror("open f1");
      return 1;
    }
    if (write(fd, "foo\n", 4) != 4)
      perror("write");
    if (fsync(fd) < 0)
      perror("fsync");
    close(fd);

    if (rename(f1, f2) < 0)
      perror("rename");

    if (fsync(dir_fd) < 0)
      perror("fsync");
  }

  return 0;
}
