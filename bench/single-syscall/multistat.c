#include <stdio.h>
#include <stdlib.h>
#include <sys/stat.h>

int
main(int ac, char** av)
{
  for (int i = 0; i < 1000000; i++) {
    struct stat st;
    stat(av[1], &st);
  }
}
