#ifndef _PARALLELIZE_H
#define _PARALLELIZE_H
typedef void (action)();
void parallel(int par, int iters, action act);
#endif
