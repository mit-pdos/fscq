#include "types.h"
#include "defs.h"

int             pipealloc(struct file** fp1, struct file** fp2) { return -1; }
void            pipeclose(struct pipe* p, int n) {}
int             piperead(struct pipe* p, char* c, int n) { return -1; }
int             pipewrite(struct pipe* p, char* c, int n) { return -1; }
