module Control.Concurrency.MonadRef

import Data.IORef
import System
import System.Info
import System.Concurrency
import System.Concurrency.MVar
import System.Future
import Data.List
-- import Data.List.Lazy
import Data.String

import Control.Relation

-- import Control.Monad.State
import System.File

import public TimeIt

import Data.String
import System.File

import Data.String
import System.File

%default total

-- Experimental module implementing a generic fork and wait interface

export
data MRef : Type -> Type where
  MkMRef : IORef (Maybe a) -> MRef a

-- This isn't legal in racket due to blocking on fork?
export
data MRefC : Type -> Type where
  MkMRefC : Channel a -> MRefC a

export
data MRefF : Type -> Type where
  MkMRefF : Future a -> MRefF a

export
data MRefMV : Type -> Type where
  MkMRefMV : MVar a -> MRefMV a

public export
interface Monad m => MonadRef m where
  RefM : Type -> Type
  fork : m a -> m (RefM a)
  read : RefM a -> m a

export
implementation [ioref]
MonadRef IO where
  RefM = MRef
  fork act = do
    r <- newIORef {a = Maybe a} Nothing
    ignore $ IO.fork (writeIORef r . Just =<< act)
    pure (MkMRef r)
  read ref@(MkMRef r) = do
    Just v <- readIORef r
      | _ => usleep 1000 *> (assert_total $ read ref) -- not good, locks up prety quickly
    pure v

export
implementation [iochan]
MonadRef IO where
  RefM = MRefC
  fork act = do
    c <- makeChannel
    ignore $ IO.fork (channelPut c =<< act)
    pure (MkMRefC c)
  read (MkMRefC c) = do
    v <- channelGet c -- block until value exists
    pure v

export
implementation [iofuture]
MonadRef IO where
  RefM = MRefF
  fork act = do
    f <- Future.forkIO act
    pure (MkMRefF f)
  read (MkMRefF f) = do
    pure (await f) -- block until value exists

export
implementation -- async: basically a future
MonadRef IO where
  RefM = MRefMV
  fork act = do
    mv <- newEmptyMVar
    _ <- IO.fork (putMVar mv =<< act)
    pure (MkMRefMV mv)
  read (MkMRefMV mv) =
    readMVar mv

-- make a MonadRef for coop lib too for fun



chunksOf : Nat -> List a -> List (List a)
chunksOf k [] = []
chunksOf k xs = let (l,r) = splitAt k xs
                in l :: assert_total (chunksOf k r)

-- :exec timeIt "waf" $ mapConcurrently (\n => sleep n <* printLn n) [7,1,2,5,4,5,6,3]
-- This is proper for IO but is it proper for other choices?
export
mapConcurrently : MonadRef m => Traversable t => (a -> m b) -> t a -> m (t b)
mapConcurrently f xs = traverse read =<< traverse (fork . f) xs

export
forConcurrently : MonadRef m => List a -> (a -> m b) -> m (List b)
forConcurrently xs f = mapConcurrently f xs

||| mapConcurrently but works in chunks. Much less efficient than worker pooling since
||| it must complete each chunk before working on the next.
export
mapConcurrentlyChunks : MonadRef m => Nat -> (a -> m b) -> List a -> m (List b)
mapConcurrentlyChunks Z f xs = traverse f xs
mapConcurrentlyChunks n f xs = do
  let bits = chunksOf n xs
  z <- traverse (mapConcurrently f) bits
  pure $ concat z

export
forConcurrentlyChunks : MonadRef m => Nat -> List a -> (a -> m b) -> m (List b)
forConcurrentlyChunks n xs f = mapConcurrentlyChunks n f xs

procs : Nat
procs = maybe 4 id (unsafePerformIO getNProcessors)

||| Thread-pooling splitting the work up among n workers, followed up with a concat
||| This is so far the fastest solution for any choice of n, but is List-specific :(
||| Default worker count matches processor count, or 4 if processor count getting fails.
||| Customize worker count by supplying a value for p: `mapConcurrentlyN {p = 4}`
export
mapConcurrentlyN : (ref : MonadRef m) => HasIO m => {default MonadRef.procs p : Nat} -> (a -> m b) -> List a -> m (List b)
mapConcurrentlyN {p = Z} f xs = traverse f xs
mapConcurrentlyN {p = n} f xs = do
    sem <- newMVar xs
    let workers = List.replicate n ()
    r <- traverse (\_ => fork $ worker sem) workers
    r2 <- traverse read r
    pure $ concat r2
  where
    worker : MVar (List a) -> m (List b)
    worker sem = do
      (x :: xs) <- takeMVar sem
        | [] => putMVar sem [] *> pure Prelude.Nil
      putMVar sem xs
      [| f x :: assert_total (worker sem) |] -- total, modulo blocking in f itself.

export
forConcurrentlyN : (ref : MonadRef m) => HasIO m => {default MonadRef.procs p : Nat} -> List a -> (a -> m b) -> m (List b)
forConcurrentlyN {p} xs f = mapConcurrentlyN {p} f xs

||| Don't use, example only.
||| Ultimatley this has too many live threads and contention.
||| Semaphor based thread-pooling allowing us to have n-workers at once without concat
||| Spawns `length xs` worker threads, but only n may work at a time.
export
mapConcurrentlyN' : (ref : MonadRef m) => HasIO m => Nat -> (a -> m b) -> List a -> m (List b)
mapConcurrentlyN' Z f xs = traverse f xs
mapConcurrentlyN' n f xs = do
    sem <- newMVar n
    traverse read =<< traverse (fork . worker sem) xs
  where
    worker : MVar Nat -> a -> m b
    worker sem x = do
      S k <- takeMVar sem
        | Z => putMVar sem Z *> assert_total (worker sem x) -- total, there will always be an S to consume eventually
      putMVar sem k
      f x <* (putMVar sem . S =<< takeMVar sem)

export
forConcurrentlyN' : (ref : MonadRef m) => HasIO m => Nat -> List a -> (a -> m b) -> m (List b)
forConcurrentlyN' n xs f = mapConcurrentlyN' n f xs

||| Semaphor based thread-pooling allowing us to have n-workers active at once without concat
||| Spawns `length xs` worker threads, but only n can work at a time.
||| Second-fastest solution for n >= 8, and doens't require List.
||| Why is this faster than mapConcurrentlyN' ?
export
mapConcurrentlyN'' : (ref : MonadRef m) => HasIO m => Traversable t => Nat -> (a -> m b) -> t a -> m (t b)
mapConcurrentlyN'' Z f xs = traverse f xs
mapConcurrentlyN'' n f xs = do
    sem <- newMVar n
    traverse read =<< traverse (worker sem) xs
  where
    worker : MVar Nat -> a -> m (RefM @{ref} b)
    worker sem x = do
      S k <- takeMVar sem
        | Z => putMVar sem Z *> assert_total (worker sem x) -- total, there will always be an S to consume eventually
      putMVar sem k
      fork $ f x <* (putMVar sem . S =<< takeMVar sem)

export
forConcurrentlyN'' : (ref : MonadRef m) => HasIO m => Nat -> List a -> (a -> m b) -> m (List b)
forConcurrentlyN'' n xs f = mapConcurrentlyN'' n f xs

