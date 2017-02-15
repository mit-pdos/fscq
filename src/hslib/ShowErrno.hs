{-# OPTIONS_GHC -fno-warn-orphans #-}

module ShowErrno where

import Foreign.C.Error
import qualified Errno

errnoToPosix :: Errno.Errno -> Errno
errnoToPosix Errno.ELOGOVERFLOW = eIO
errnoToPosix Errno.ENOTDIR      = eNOTDIR
errnoToPosix Errno.EISDIR       = eISDIR
errnoToPosix Errno.ENOENT       = eNOENT
errnoToPosix Errno.EFBIG        = eFBIG
errnoToPosix Errno.ENAMETOOLONG = eNAMETOOLONG
errnoToPosix Errno.EEXIST       = eEXIST
errnoToPosix Errno.ENOSPCBLOCK  = eNOSPC
errnoToPosix Errno.ENOSPCINODE  = eNOSPC
errnoToPosix Errno.ENOTEMPTY    = eNOTEMPTY
errnoToPosix Errno.EINVAL       = eINVAL

instance Show Errno.Errno where
  show Errno.ELOGOVERFLOW = "ELOGOVERFLOW"
  show Errno.ENOTDIR      = "ENOTDIR"
  show Errno.EISDIR       = "EISDIR"
  show Errno.ENOENT       = "ENOENT"
  show Errno.EFBIG        = "EFBIG"
  show Errno.ENAMETOOLONG = "ENAMETOOLONG"
  show Errno.EEXIST       = "EEXIST"
  show Errno.ENOSPCBLOCK  = "ENOSPCBLOCK"
  show Errno.ENOSPCINODE  = "ENOSPCINODE"
  show Errno.ENOTEMPTY    = "ENOTEMPTY"
  show Errno.EINVAL       = "EINVAL"

instance Show t => Show (Errno.Coq_res t) where
  show (Errno.OK v) = show v
  show (Errno.Err e) = show e
