#include <fcntl.h>
#include <unistd.h>
#include <stdio.h>

int main(int argc, char *argv[]) {
	if (argc < 2) {
		return 1;
	}
	for (int i = 0; i < 50000; i++) {
		int fd = open(argv[1], O_RDONLY);
		close(fd);
	}
	return 0;
}
