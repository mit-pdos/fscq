# Overview

There are two high level questions: how much I/O concurrency does CFSCQ provide? and, how much read-only parallelism does CFSCQ provide?

## Focused questions

1. Does CFSCQ effectively parallelize read-only metadata operations?
2. Does CFSCQ effectively parallelize data reads?
   these actually exercise the concurrent cache
3. Does CFSCQ have I/O concurrency?
4. Does CFSCQ have acceptable overhead for sequential workloads?
5. Does CFSCQ perform acceptably with writes?
   won't improve performance, and perf degradation should be low

# Results

- parallel metadata operations
- parallel disk reads
- cold cache I/O concurrency

Broadly:
- FSCQ and CFSCQ are fast at metadata operations and slow with data.
- CFSCQ adds low overhad (~10%), and parallelizes well (~3.5x on 4 cores) for warm workloads.
- CFSCQ is much slower (around 2x) than FSCQ at filling data into the cache.
- FSCQ indeed blocks CPU operations behind I/O, although this is mostly masked by the sequential overhead.

# Insights

## Disk prefetching gives FSCQ I/O concurrency

Linux preads are observed to have prefetching, and coincidentally we spend about as much CPU time as disk reads, so that FSCQ observes nearly perfect I/O concurrency. Specifically, disk latency is so perfectly hidden by I/O concurrency that a physical disk and in-memory disk have about the same performance.

Addressed by reading files in random order. Alternately, opening with `O_DIRECT` does solve the problem (from a C benchmark), but this is awkward to fix in Haskell since the standard library doesn't allow passing `O_DIRECT` (we'd also have to align the read buffer).

## CFSCQ re-executes code

CFSCQ must have some overhead due to re-execution, and this is significant in CPU-bottlenecked workloads. One case is avoidable: upon a cache miss during read-only execution, we can forward the missed address in order to read it immediately once we have the write lock.

## CFSCQ translation impact

The impact of translation is still unclear, since it seemingly impacts overall execution more than any particular function. Still can't conclusively say compilation has helped.

## Debug output is extremely slow

Executing debug instructions (which writes to stdout) is extremely slow and skews measurements if timings are nested.

Solved by buffering debug info, with the additional precaution of only recording aggregate statistics. The main cost is constructing the debug strings (which we do as a `String`).

## Reading data was generally slow in CFSCQ

Profiles showed `i2buf` in CFSCQ but not in FSCQ - turns out FSCQ now uses `w2bs` for some word/buffer manipulation, which hadn't been ported to the `read_piece` implementation in `CfscqFs.hs`.

# Mysteries

Why is CFSCQ faster than FSCQ for statfs and stat?
- statfs is mostly measuring Haskell code to get `fsxp` and `mscs`, so its understandable
- `stat` is odd, but it's also really fast and probably unrelated to the overall performance story

What is the impact of compiling away translation?
- for `read_attr` has no impact, and for `read_fblock` seems to make things worse (from 1.13x to 2.23x compared to FSCQ)

Why is reading files so much slower than FSCQ for warm workloads?
- at least in part due to a missing FSCQ optimization

Where exactly does CFSCQ's sequential overhead come from?

Why does traversing a directory not parallelize beyond 2x?
