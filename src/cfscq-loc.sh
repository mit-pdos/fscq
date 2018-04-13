#!/bin/sh

count() {
  cloc --include-lang=Coq,Haskell --quiet --csv "$@"
  echo
}

echo "Execution semantics"
count \
    CCLProg.v \
    CCLMonadLaws.v \
    CCLHoareTriples.v \
    CCLPrimitives.v \
    CCLHashExec.v \
    Automation.v \
    CCLAutomation.v \
    CCL.v

echo "Concurrent virtual disk"
count \
    MemCache.v \
    OptimisticCache.v

echo "Translator"
count \
    SeqSpecs.v \
    OptimisticTranslator.v \
    OptimisticFS.v \
    OptimisticFSSpecs.v

echo "Retry stub"
count \
    RetryLoop.v \
    FSProtocol.v \
    ConcurrentFS.v

echo "Haskell"
count \
    hslib/ConcurInterp.hs \
    hslib/ShowErrno.hs \
    hslib/CfscqFs.hs \
    cfscq.hs

echo "app - protocol"
count \
    HomeDirProtocol.v

echo "app - copy impl"
count \
    ConcurrentCopy.v
