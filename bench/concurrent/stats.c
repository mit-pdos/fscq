#include <fcntl.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/stat.h>

int main(int argc, char *argv[]) {
	if (argc < 3) {
		return 1;
	}
  int iters = atoi(argv[2]) * 1000;
	struct stat buf;
	for (int i = 0; i < iters; i++) {
		stat(argv[1], &buf);
	}
	return 0;
}
