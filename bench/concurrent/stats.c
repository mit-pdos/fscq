#include <fcntl.h>
#include <unistd.h>
#include <stdio.h>
#include <sys/stat.h>

int main(int argc, char *argv[]) {
	if (argc < 2) {
		return 1;
	}
	struct stat buf;
	for (int i = 0; i < 25000; i++) {
		stat(argv[1], &buf);
	}
	return 0;
}
