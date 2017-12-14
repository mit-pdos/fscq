module Main where

import           CfscqFs
import           Control.Monad.State
import qualified Data.Map.Strict as Map
import           Data.Text as T
import           DbenchScript
import           Foreign.C.Error
import           FscqFs
import           Fuse
import           System.Posix.Files (stdFileMode)
import           System.Posix.IO

type HandleMapping = Map.Map String Handle

expectStatus :: ExpectedStatus -> Either Errno a -> IO ()
expectStatus StatusOk           (Right _) = return ()
-- TODO: check that the error number is correct
expectStatus StatusNameNotFound (Left _) = return ()
expectStatus StatusPathNotFound (Left _) = return ()
expectStatus StatusNoSuchFile   (Left _) = return ()
expectStatus StatusOk           (Left e) = ioError (errnoToIOError "" e Nothing Nothing)
expectStatus s                  (Right _) = ioError (userError $ "expected failure " ++ show s)

runCommand :: FuseOperations fh -> Command -> StateT HandleMapping IO ()
runCommand fs (CreateX (Path p) _ _ h s) = do
  modify (Map.insert p h)
  liftIO $ do
    r <- fuseCreateFile fs p stdFileMode ReadWrite defaultFileFlags
    expectStatus s r

runScript :: FuseOperations fh -> Script -> IO ()
runScript fs s = evalStateT (mapM_ (runCommand fs) s) Map.empty

main :: IO ()
main = return ()
