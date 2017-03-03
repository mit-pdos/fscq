{-# LANGUAGE CPP
           , DeriveDataTypeable
           , NamedFieldPuns
           , NoImplicitPrelude
  #-}

#if __GLASGOW_HASKELL__ >= 704
{-# LANGUAGE Safe #-}
#endif

-------------------------------------------------------------------------------
-- |
-- Module     : Control.Concurrent.ReadWriteLock
-- Copyright  : (c) 2010-2011 Bas van Dijk & Roel van Dijk
-- License    : BSD3 (see the file LICENSE)
-- Maintainer : Bas van Dijk <v.dijk.bas@gmail.com>
--            , Roel van Dijk <vandijk.roel@gmail.com>
--
-- Multiple-reader, single-writer locks. Used to protect shared resources which
-- may be concurrently read, but only sequentially written.
--
-- All functions are /exception safe/. Throwing asynchronous exceptions will not
-- compromise the internal state of an 'RWLock'. This means it is perfectly safe
-- to kill a thread that is blocking on, for example, 'acquireRead'.
--
-- See also Java's version:
-- <http://java.sun.com/javase/7/docs/api/java/util/concurrent/locks/ReadWriteLock.html>
--
-- This module is designed to be imported qualified. We suggest importing it
-- like:
--
-- @
-- import           Control.Concurrent.ReadWriteLock        ( RWLock )
-- import qualified Control.Concurrent.ReadWriteLock as RWL ( ... )
-- @
--
-------------------------------------------------------------------------------

module ReadWriteLock
  ( RWLock

    -- *Creating Read-Write Locks
  , new
  , newAcquiredRead
  , newAcquiredWrite

    -- *Read access
    -- **Blocking
  , acquireRead
  , releaseRead
  , withRead
  , waitRead
    -- **Non-blocking
  , tryAcquireRead
  , tryWithRead

    -- *Write access
    -- **Blocking
  , acquireWrite
  , releaseWrite
  , withWrite
  , waitWrite
    -- **Non-blocking
  , tryAcquireWrite
  , tryWithWrite
  ) where


-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

-- from base:
import Control.Applicative     ( liftA2, liftA3 )
import Control.Concurrent.MVar ( MVar, newMVar, takeMVar, putMVar )
import Control.Exception       ( bracket_, onException )
import Control.Monad           ( return, (>>) )
import Data.Bool               ( Bool(False, True) )
import Data.Eq                 ( Eq, (==) )
import Data.Function           ( ($), (.), on )
import Data.Int                ( Int )
import Data.Maybe              ( Maybe(Nothing, Just) )
import Data.List               ( (++))
import Data.Typeable           ( Typeable )
import Prelude                 ( String, ($!), succ, pred, error )
import System.IO               ( IO )

#if __GLASGOW_HASKELL__ < 700
import Prelude                 ( fromInteger )
import Control.Monad           ( (>>=), fail )
#endif

-- from concurrent-extra (this package):
import           Control.Concurrent.Lock ( Lock )
import qualified Control.Concurrent.Lock as Lock
    ( new, newAcquired, acquire, release, wait )

import Utils ( mask, mask_ )


-------------------------------------------------------------------------------
-- Read Write Lock
-------------------------------------------------------------------------------

{-|
Multiple-reader, single-writer lock. Is in one of three states:
* \"Free\": Read or write access can be acquired without blocking.
* \"Read\": One or more threads have acquired read access. Blocks write access.
* \"Write\": A single thread has acquired write access. Blocks other threads
from acquiring both read and write access.
-}
data RWLock = RWLock { state     :: MVar State
                     , readLock  :: Lock
                     , writeLock :: Lock
                     } deriving Typeable

instance Eq RWLock where
    (==) = (==) `on` state

-- | Internal state of the 'RWLock'.
data State = Free | Read Int | Write


-------------------------------------------------------------------------------
-- * Creating Read-Write Locks
-------------------------------------------------------------------------------

-- | Create a new 'RWLock' in the \"free\" state; either read or write access
-- can be acquired without blocking.
new :: IO RWLock
new = liftA3 RWLock (newMVar Free)
                    Lock.new
                    Lock.new

-- | Create a new 'RWLock' in the \"read\" state; only read can be acquired
-- without blocking.
newAcquiredRead :: IO RWLock
newAcquiredRead = liftA3 RWLock (newMVar $ Read 1)
                                Lock.newAcquired
                                Lock.new

-- | Create a new 'RWLock' in the \"write\" state; either acquiring read or
-- write will block.
newAcquiredWrite :: IO RWLock
newAcquiredWrite = liftA3 RWLock (newMVar Write)
                                 Lock.new
                                 Lock.newAcquired


-------------------------------------------------------------------------------
-- * Read access
-------------------------------------------------------------------------------

{-|
Acquire the read lock.
Blocks if another thread has acquired write access. If @acquireRead@ terminates
without throwing an exception the state of the 'RWLock' will be \"read\".
Implementation note: Throws an exception when more than (maxBound :: Int)
simultaneous threads acquire the read lock. But that is unlikely.
-}
acquireRead :: RWLock -> IO ()
acquireRead (RWLock {state, readLock, writeLock}) = mask_ acqRead
    where
      acqRead = do st <- takeMVar state
                   case st of
                     Free   -> do Lock.acquire readLock
                                  putMVar state $ Read 1
                     Read n -> putMVar state . Read $! succ n
                     Write  -> do putMVar state st
                                  Lock.wait writeLock
                                  acqRead

{-|
Try to acquire the read lock; non blocking.
Like 'acquireRead', but doesn't block. Returns 'True' if the resulting state is
\"read\", 'False' otherwise.
-}
tryAcquireRead :: RWLock -> IO Bool
tryAcquireRead (RWLock {state, readLock}) = mask_ $ do
  st <- takeMVar state
  case st of
    Free   -> do Lock.acquire readLock
                 putMVar state $ Read 1
                 return True
    Read n -> do putMVar state . Read $! succ n
                 return True
    Write  -> do putMVar state st
                 return False

{-|
Release the read lock.
If the calling thread was the last one to relinquish read access the state will
revert to \"free\".
It is an error to release read access to an 'RWLock' which is not in the
\"read\" state.
-}
releaseRead :: RWLock -> IO ()
releaseRead (RWLock {state, readLock}) = mask_ $ do
  st <- takeMVar state
  case st of
    Read 1 -> do Lock.release readLock
                 putMVar state Free
    Read n -> putMVar state . Read $! pred n
    _ -> do putMVar state st
            error $ moduleName ++ ".releaseRead: already released"

{-|
A convenience function wich first acquires read access and then performs the
computation. When the computation terminates, whether normally or by raising an
exception, the read lock is released.
-}
withRead :: RWLock -> IO a -> IO a
withRead = liftA2 bracket_ acquireRead releaseRead

{-|
A non-blocking 'withRead'. First tries to acquire the lock. If that fails,
'Nothing' is returned. If it succeeds, the computation is performed. When the
computation terminates, whether normally or by raising an exception, the lock is
released and 'Just' the result of the computation is returned.
-}
tryWithRead :: RWLock -> IO a -> IO (Maybe a)
tryWithRead l a = mask $ \restore -> do
  acquired <- tryAcquireRead l
  if acquired
    then do r <- restore a `onException` releaseRead l
            releaseRead l
            return $ Just r
    else return Nothing

{-|
* When the state is \"write\", @waitRead@ /blocks/ until a call to
'releaseWrite' in another thread changes the state to \"free\".
* When the state is \"free\" or \"read\" @waitRead@ returns immediately.
@waitRead@ does not alter the state of the lock.
Note that @waitRead@ is just a convenience function defined as:
@waitRead l = 'mask_' '$' 'acquireRead' l '>>' 'releaseRead' l@
-}
waitRead :: RWLock -> IO ()
waitRead l = mask_ $ acquireRead l >> releaseRead l


-------------------------------------------------------------------------------
-- *Write access
-------------------------------------------------------------------------------

{-|
Acquire the write lock.
Blocks if another thread has acquired either read or write access. If
@acquireWrite@ terminates without throwing an exception the state of the
'RWLock' will be \"write\".
-}
acquireWrite :: RWLock -> IO ()
acquireWrite (RWLock {state, readLock, writeLock}) = mask_ acqWrite
    where
      acqWrite = do st <- takeMVar state
                    case st of
                      Free   -> do Lock.acquire writeLock
                                   putMVar state Write
                      Read _ -> do putMVar state st
                                   Lock.wait readLock
                                   acqWrite
                      Write  -> do putMVar state st
                                   Lock.wait writeLock
                                   acqWrite

{-|
Try to acquire the write lock; non blocking.
Like 'acquireWrite', but doesn't block. Returns 'True' if the resulting state is
\"write\", 'False' otherwise.
-}
tryAcquireWrite :: RWLock -> IO Bool
tryAcquireWrite (RWLock {state, writeLock}) = mask_ $ do
  st <- takeMVar state
  case st of
    Free   -> do Lock.acquire writeLock
                 putMVar state Write
                 return True
    _      -> do putMVar state st
                 return False

{-|
Release the write lock.
If @releaseWrite@ terminates without throwing an exception the state will be
\"free\".
It is an error to release write access to an 'RWLock' which is not in the
\"write\" state.
-}
releaseWrite :: RWLock -> IO ()
releaseWrite (RWLock {state, writeLock}) = mask_ $ do
  st <- takeMVar state
  case st of
    Write -> do Lock.release writeLock
                putMVar state Free
    _ -> do putMVar state st
            error $ moduleName ++ ".releaseWrite: already released"

{-|
A convenience function wich first acquires write access and then performs
the computation. When the computation terminates, whether normally or by raising
an exception, the write lock is released.
-}
withWrite :: RWLock -> IO a -> IO a
withWrite = liftA2 bracket_ acquireWrite releaseWrite

{-|
A non-blocking 'withWrite'. First tries to acquire the lock. If that fails,
'Nothing' is returned. If it succeeds, the computation is performed. When the
computation terminates, whether normally or by raising an exception, the lock is
released and 'Just' the result of the computation is returned.
-}
tryWithWrite :: RWLock -> IO a -> IO (Maybe a)
tryWithWrite l a = mask $ \restore -> do
  acquired <- tryAcquireWrite l
  if acquired
    then do r <- restore a `onException` releaseWrite l
            releaseWrite l
            return $ Just r
    else return Nothing

{-|
* When the state is \"write\" or \"read\" @waitWrite@ /blocks/ until a call to
'releaseWrite' or 'releaseRead' in another thread changes the state to \"free\".
* When the state is \"free\" @waitWrite@ returns immediately.
@waitWrite@ does not alter the state of the lock.
Note that @waitWrite@ is just a convenience function defined as:
@waitWrite l = 'mask_' '$' 'acquireWrite' l '>>' 'releaseWrite' l@
-}
waitWrite :: RWLock -> IO ()
waitWrite l = mask_ $ acquireWrite l >> releaseWrite l

moduleName :: String
moduleName = "Control.Concurrent.ReadWriteLock"
