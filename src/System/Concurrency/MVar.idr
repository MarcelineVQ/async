module System.Concurrency.MVar

import System.Concurrency
import Data.IORef

-- I make the decision to assert_total in this module because we're already blocking
-- on these. Either that's correct, or double-wrong to do.

-- Some mistakes early in this modules creation would have been avoided by making
-- an indexed monad of actions that enforced mutex aquires and releases, and possibly
-- wait conditions too. In particular mutex release was forgotten in the `_ => ...` branches

-- This version of MVar has no particular/proven fairness guarantees

||| The type of thread-safe mutable boxes which are always either empty or full.
||| Value is in IORef in order to treat mutably and guarantee IO ordering
export
data MVar : Type -> Type where
  MkMVar : (lock : Mutex) -> (take : Condition) -> (put : Condition) -> IORef (Maybe a) -> MVar a

export
newMVar : HasIO io => a -> io (MVar a)
newMVar x = [| MkMVar makeMutex makeCondition makeCondition (newIORef (Just x)) |]

export
newEmptyMVar : HasIO io => io (MVar a)
newEmptyMVar = [| MkMVar makeMutex makeCondition makeCondition (newIORef Nothing) |]

export
putMVar :  HasIO io => MVar a -> a -> io ()
putMVar mv@(MkMVar m tc pc r) x = do
  mutexAcquire m
  Nothing <- readIORef r
    | _ => conditionWait pc m *> mutexRelease m *> (assert_total $ putMVar mv x {- TODO: Not total! -})
  writeIORef r (Just x)
  conditionSignal tc
  mutexRelease m

export
tryPutMVar : HasIO io => MVar a -> a -> io Bool
tryPutMVar (MkMVar m tc pc r) x = do
  mutexAcquire m
  Nothing <- readIORef r
    | _ => mutexRelease m *> pure False
  writeIORef r (Just x)
  conditionSignal tc
  mutexRelease m
  pure True

export
takeMVar : HasIO io => MVar a -> io a
takeMVar mv@(MkMVar m tc pc r) = do
  mutexAcquire m
  Just x <- readIORef r
    | _ => conditionWait tc m *> mutexRelease m *> (assert_total $ takeMVar mv {- TODO: Not total! -})
  writeIORef r Nothing
  conditionSignal pc
  mutexRelease m
  pure x

export
tryTakeMVar : HasIO io => MVar a -> io (Maybe a)
tryTakeMVar (MkMVar m tc pc r) = do
  mutexAcquire m
  v@(Just _) <- readIORef r
    | _ => mutexRelease m *> pure Nothing
  writeIORef r Nothing
  conditionSignal pc
  mutexRelease m
  pure v

-- is this right? is mutex enough blocking? should this `conditionSignal tc` like modify does?
-- Is this `too` blocking with the conditionWait?
export
readMVar : HasIO io => MVar a -> io a
readMVar mv@(MkMVar m tc pc r) = do
  mutexAcquire m
  Just x <- readIORef r
    | _ => conditionWait tc m *> mutexRelease m *> (assert_total $ readMVar mv {- TODO: Not total! -})
  mutexRelease m
  pure x

export
modifyMVar : HasIO io => MVar a -> (a -> io (a, b)) -> io b
modifyMVar mv@(MkMVar m tc pc r) f = do
  mutexAcquire m
  Just v <- readIORef r
    | _ => conditionWait tc m *> mutexRelease m *> (assert_total $ modifyMVar mv f {- TODO: Not total! -})
  (x,y) <- f v
  writeIORef r (Just x)
  conditionSignal tc
  mutexRelease m
  pure y

export
modifyMVar_ : HasIO io => MVar a -> (a -> io a) -> io ()
modifyMVar_ mv f = modifyMVar mv (map (,()) . f)
