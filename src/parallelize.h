#ifndef _PARALLELIZE_H
#define _PARALLELIZE_H
typedef void (action)();
void parallel(int n, action act);
#endif
