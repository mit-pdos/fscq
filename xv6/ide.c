#include "types.h"
#include "defs.h"
#include "fs.h"
#include "buf.h"

void unix_read(int sector, unsigned char *buf, int sz);
void unix_write(int sector, unsigned char *buf, int sz);
void unix_flush(void);

void iderw(struct buf *b) {
  if(!(b->flags & B_BUSY))
    panic("iderw: buf not busy");
  if((b->flags & (B_VALID|B_DIRTY)) == B_VALID)
    panic("iderw: nothing to do");

  if (b->flags & B_DIRTY) {
    unix_write(b->sector, b->data, BSIZE);
    b->flags &= ~B_DIRTY;
  } else {
    unix_read(b->sector, b->data, BSIZE);
    b->flags |= B_VALID;
  }
}

void ideflush() {
  unix_flush();
}
