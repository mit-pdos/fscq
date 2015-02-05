module Main where

import qualified Data.ByteString.Char8 as B
import Foreign.C.Error
import System.Posix.Types
import System.Posix.Files
import System.Posix.IO

import System.Fuse

type HT = ()

main :: IO ()
main = fuseMain helloFSOps defaultExceptionHandler

helloFSOps :: FuseOperations HT
helloFSOps = defaultFuseOps { fuseGetFileStat = helloGetFileStat
                            , fuseOpen        = helloOpen
                            , fuseRead        = helloRead 
                            , fuseOpenDirectory = helloOpenDirectory
                            , fuseReadDirectory = helloReadDirectory
                            , fuseGetFileSystemStats = helloGetFileSystemStats
                            }
helloString :: B.ByteString
helloString = B.pack "Hello World, HFuse!\n"

helloPath :: FilePath
helloPath = "/hello"
dirStat ctx = FileStat { statEntryType = Directory
                       , statFileMode = foldr1 unionFileModes
                                          [ ownerReadMode
                                          , ownerExecuteMode
                                          , groupReadMode
                                          , groupExecuteMode
                                          , otherReadMode
                                          , otherExecuteMode
                                          ]
                       , statLinkCount = 2
                       , statFileOwner = fuseCtxUserID ctx
                       , statFileGroup = fuseCtxGroupID ctx
                       , statSpecialDeviceID = 0
                       , statFileSize = 4096
                       , statBlocks = 1
                       , statAccessTime = 0
                       , statModificationTime = 0
                       , statStatusChangeTime = 0
                       }

fileStat ctx = FileStat { statEntryType = RegularFile
                        , statFileMode = foldr1 unionFileModes
                                           [ ownerReadMode
                                           , groupReadMode
                                           , otherReadMode
                                           ]
                        , statLinkCount = 1
                        , statFileOwner = fuseCtxUserID ctx
                        , statFileGroup = fuseCtxGroupID ctx
                        , statSpecialDeviceID = 0
                        , statFileSize = fromIntegral $ B.length helloString
                        , statBlocks = 1
                        , statAccessTime = 0
                        , statModificationTime = 0
                        , statStatusChangeTime = 0
                        }

helloGetFileStat :: FilePath -> IO (Either Errno FileStat)
helloGetFileStat "/" = do
    ctx <- getFuseContext
    return $ Right $ dirStat ctx
helloGetFileStat path | path == helloPath = do
    ctx <- getFuseContext
    return $ Right $ fileStat ctx
helloGetFileStat _ =
    return $ Left eNOENT

helloOpenDirectory "/" = return eOK
helloOpenDirectory _   = return eNOENT

helloReadDirectory :: FilePath -> IO (Either Errno [(FilePath, FileStat)])
helloReadDirectory "/" = do
    ctx <- getFuseContext
    return $ Right [(".",          dirStat  ctx)
                   ,("..",         dirStat  ctx)
                   ,(helloName,    fileStat ctx)
                   ]
    where (_:helloName) = helloPath
helloReadDirectory _ = return (Left (eNOENT))

helloOpen :: FilePath -> OpenMode -> OpenFileFlags -> IO (Either Errno HT)
helloOpen path mode flags
    | path == helloPath = case mode of
                            ReadOnly -> return (Right ())
                            _        -> return (Left eACCES)
    | otherwise         = return (Left eNOENT)


helloRead :: FilePath -> HT -> ByteCount -> FileOffset -> IO (Either Errno B.ByteString)
helloRead path _ byteCount offset
    | path == helloPath =
        return $ Right $ B.take (fromIntegral byteCount) $ B.drop (fromIntegral offset) helloString
    | otherwise         = return $ Left eNOENT

helloGetFileSystemStats :: String -> IO (Either Errno FileSystemStats)
helloGetFileSystemStats str =
  return $ Right $ FileSystemStats
    { fsStatBlockSize = 512
    , fsStatBlockCount = 1
    , fsStatBlocksFree = 1
    , fsStatBlocksAvailable = 1
    , fsStatFileCount = 5
    , fsStatFilesFree = 10
    , fsStatMaxNameLength = 255
    }
