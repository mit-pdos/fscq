#!/usr/bin/env python2

import sys
import collections

active = False
gc_start = None
scope_stack = []
scope_cost = collections.defaultdict(int)

for l in sys.stdin.readlines():
  l = l.strip()
  if l == 'Events:':
    active = True
    continue

  if active and ':' in l:
    (ts, ev) = l.split(':', 1)
    ts = int(ts)
    ev = ev.strip()
    if ev.startswith('cap '):
      (_, msg) = ev.split(':', 1)
      msg = msg.strip()
      if msg == 'starting GC':
        gc_start = ts
      if msg == 'finished GC':
        gc_time = ts - gc_start
        gc_start = None
        scope_stack = [(scope, ts + gc_time) for (scope, ts) in scope_stack]

      if msg.startswith('START'):
        scope = msg[6:]
        scope_stack.append((scope, ts))

      if msg.startswith('STOP'):
        scope = msg[5:]
        while True:
          (last_scope, last_ts) = scope_stack.pop()
          scope_cost[last_scope] += ts - last_ts
          if scope == last_scope:
            break

for (scope, cost) in scope_cost.iteritems():
  print "%2.3f %s" % (cost/1.0e9, scope)
