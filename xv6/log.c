#include "types.h"
#include "defs.h"
#include "param.h"
#include "spinlock.h"
#include "fs.h"
#include "buf.h"
#ifdef FUSEFS
#include "string.h"
#endif

// Simple logging that allows concurrent FS system calls.
//
// A log transaction contains the updates of multiple FS system
// calls. The logging system only commits when there are
// no FS system calls active. Thus there is never
// any reasoning required about whether a commit might
// write an uncommitted system call's updates to disk.
//
// A system call should call begin_op()/end_op() to mark
// its start and end. Usually begin_op() just increments
// the count of in-progress FS system calls and returns.
// But if it thinks the log is close to running out, it
// sleeps until the last outstanding end_op() commits.
//
// The log is a physical re-do log containing disk blocks.
// The on-disk log format:
//   header block, containing sector #s for block A, B, C, ...
//   block A
//   block B
//   block C
//   ...
// Log appends are synchronous.

// Contents of the header block, used for both the on-disk header block
// and to keep track in memory of logged sector #s before commit.
struct logheader {
  int n;   
  int sector[LOGSIZE];
};

struct log {
  struct spinlock lock;
  int start;
  int size;
  int outstanding; // how many FS sys calls are executing.
  int committing;  // in commit(), please wait.
  int dev;
  struct logheader lh;
};

struct log thelog;

static void recover_from_log(void);
static void commit();

void
initlog(void)
{
  if (sizeof(struct logheader) >= BSIZE)
    panic("initlog: too big logheader");

  struct superblock sb;
  initlock(&thelog.lock, "log");
  readsb(ROOTDEV, &sb);
  thelog.start = sb.size - sb.nlog;
  thelog.size = sb.nlog;
  thelog.dev = ROOTDEV;
  recover_from_log();
}

// Copy committed blocks from log to their home location
static void 
install_trans(void)
{
  int tail;

  for (tail = 0; tail < thelog.lh.n; tail++) {
    struct buf *lbuf = bread(thelog.dev, thelog.start+tail+1); // read log block
    struct buf *dbuf = bread(thelog.dev, thelog.lh.sector[tail]); // read dst
    memmove(dbuf->data, lbuf->data, BSIZE);  // copy block to dst
    bwrite(dbuf);  // write dst to disk
    brelse(lbuf); 
    brelse(dbuf);
  }
}

// Read the log header from disk into the in-memory log header
static void
read_head(void)
{
  struct buf *b = bread(thelog.dev, thelog.start);
  struct logheader *lh = (struct logheader *) (b->data);
  int i;
  thelog.lh.n = lh->n;
  for (i = 0; i < thelog.lh.n; i++) {
    thelog.lh.sector[i] = lh->sector[i];
  }
  brelse(b);
}

// Write in-memory log header to disk.
// This is the true point at which the
// current transaction commits.
static void
write_head(void)
{
  ideflush();   // flush all preceding writes to disk
  struct buf *buf = bread(thelog.dev, thelog.start);
  struct logheader *hb = (struct logheader *) (buf->data);
  int i;
  hb->n = thelog.lh.n;
  for (i = 0; i < thelog.lh.n; i++) {
    hb->sector[i] = thelog.lh.sector[i];
  }
  bwrite(buf);
  ideflush();   // flush head
  brelse(buf);
}

static void
recover_from_log(void)
{
  read_head();      
  install_trans(); // if committed, copy from log to disk
  thelog.lh.n = 0;
  write_head(); // clear the log
}

// called at the start of each FS system call.
void
begin_op(void)
{
  acquire(&thelog.lock);
  while(1){
    if(thelog.committing){
      sleep(&thelog, &thelog.lock);
    } else if(thelog.lh.n + (thelog.outstanding+1)*MAXOPBLOCKS > LOGSIZE){
      // this op might exhaust log space; wait for commit.
      sleep(&thelog, &thelog.lock);
    } else {
      thelog.outstanding += 1;
      release(&thelog.lock);
      break;
    }
  }
}

// called at the end of each FS system call.
// commits if this was the last outstanding operation.
void
end_op(void)
{
  int do_commit = 0;

  acquire(&thelog.lock);
  thelog.outstanding -= 1;
  if(thelog.committing)
    panic("thelog.committing");
  if(thelog.outstanding == 0){
    do_commit = 1;
    thelog.committing = 1;
  } else {
    // begin_op() may be waiting for log space.
    wakeup(&thelog);
  }
  release(&thelog.lock);

  if(do_commit){
    // call commit w/o holding locks, since not allowed
    // to sleep with locks.
    commit();
    acquire(&thelog.lock);
    thelog.committing = 0;
    wakeup(&thelog);
    release(&thelog.lock);
  }
}

// Copy modified blocks from cache to thelog.
static void 
write_log(void)
{
  int tail;

  for (tail = 0; tail < thelog.lh.n; tail++) {
    struct buf *to = bread(thelog.dev, thelog.start+tail+1); // log block
    struct buf *from = bread(thelog.dev, thelog.lh.sector[tail]); // cache block
    memmove(to->data, from->data, BSIZE);
    bwrite(to);  // write the log
    brelse(from); 
    brelse(to);
  }
}

static void
commit()
{
  if (thelog.lh.n > 0) {
    write_log();     // Write modified blocks from cache to log
    write_head();    // Write header to disk -- the real commit
    install_trans(); // Now install writes to home locations
    thelog.lh.n = 0; 
    write_head();    // Erase the transaction from the log
  }
}

// Caller has modified b->data and is done with the buffer.
// Record the block number and pin in the cache with B_DIRTY.
// commit()/write_log() will do the disk write.
//
// log_write() replaces bwrite(); a typical use is:
//   bp = bread(...)
//   modify bp->data[]
//   log_write(bp)
//   brelse(bp)
void
log_write(struct buf *b)
{
  int i;

  if (thelog.lh.n >= LOGSIZE || thelog.lh.n >= thelog.size - 1)
    panic("too big a transaction");
  if (thelog.outstanding < 1)
    panic("log_write outside of trans");

  for (i = 0; i < thelog.lh.n; i++) {
    if (thelog.lh.sector[i] == b->sector)   // log absorbtion
      break;
  }
  thelog.lh.sector[i] = b->sector;
  if (i == thelog.lh.n)
    thelog.lh.n++;
  b->flags |= B_DIRTY; // prevent eviction
}

