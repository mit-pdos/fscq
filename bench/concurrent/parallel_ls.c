#include <dirent.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

struct operation {
  char *path;
};

void* read_entire_dir(void *arg) {
  struct operation *op = (struct operation*) arg;
  DIR *dirp = opendir(op->path);
  while (readdir(dirp) != NULL) {}
  return NULL;
}

int main(int argc, char *argv[]) {
  if (argc < 3) {
    fprintf(stderr, "Usage: %s <n> <path>", argv[0]);
    return 1;
  }
  int num = atoi(argv[1]);
  char *path = argv[2];

  if (num == 0) {
    return 2;
  }

  pthread_t *ts = calloc(num, sizeof(pthread_t));

  struct operation op = {path};

  for (int i = 0; i < num; i++) {
    pthread_create(&ts[i], NULL, &read_entire_dir, (void*) &op);
  }

  for (int i = 0; i < num; i++) {
    pthread_join(ts[i], NULL);
  }

  return 0;
}
