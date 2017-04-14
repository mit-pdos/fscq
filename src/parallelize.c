#include "parallelize.h"

void parallel(int n, action act) {
  // TODO: do these in parallel, not sequentially
  for (int i = 0; i < n; i++) {
    act();
  }
}
