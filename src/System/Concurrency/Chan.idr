module System.Concurrency.Chan

import System.Concurrency.MVar

%hide Prelude.Types.Stream.Stream

-- MVar based unbounded channels

public export
data Item : Type -> Type where
  MkItem : a -> Inf (MVar (Item a)) -> Item a

public export
Stream : Type -> Type
Stream a = MVar (Item a)

public export
record Chan a where
  constructor MkChan
  readVar : MVar (Stream a) -- readVar contains the readEnd
  writeVar : MVar (Stream a) -- writeVar contains the writeEnd

export
newChan : HasIO io => io (Chan a)
newChan = do
    hole <- newEmptyMVar
    readVar <- newMVar hole
    writeVar <- newMVar hole
    pure $ MkChan readVar writeVar

export
readChan : HasIO io => Chan a -> io a
readChan chan = do
  stream <- takeMVar chan.readVar
  MkItem a as <- readMVar stream
  putMVar chan.readVar as
  pure a

export
writeChan : HasIO io => Chan a -> a -> io ()
writeChan chan v = do
  newHole <- newEmptyMVar
  oldHole <- takeMVar chan.writeVar
  putMVar oldHole (MkItem v newHole)
  putMVar chan.writeVar newHole

||| Create an initlly empty channel that then receives the same updates as another
export
dupChan : HasIO io => Chan a -> io (Chan a)
dupChan chan = do
  hole <- readMVar chan.writeVar -- get the source chan's end hole
  newReadEnd <- newMVar hole -- make a new MVar around it
  pure $ MkChan newReadEnd chan.writeVar -- we now share the end hole
