#include <fcntl.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char *argv[]) {
	if (argc < 3) {
		return 1;
	}
	int iters = atoi(argv[2]) * 1000;
	for (int i = 0; i < iters; i++) {
		int fd = open(argv[1], O_RDONLY);
		close(fd);
	}
	return 0;
}
