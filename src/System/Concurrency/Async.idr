module System.Concurrency.Async

import System.Concurrency.MVar

-- MVar based asychronisity

data Async a = MkAsync (MVar a)

async : IO a -> IO (Async a)
async action = do
  var <- newEmptyMVar
  _ <- fork (putMVar var =<< action)
  pure (MkAsync var)

wait : Async a -> IO a
wait (MkAsync var) = readMVar var


