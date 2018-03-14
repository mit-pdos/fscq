{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module DataSet
  ( DataValue
  , kv
  , dataHeader
  , dataRow
  ) where

import Data.List (intercalate)

data DataValue = DataValue { key :: String, value :: String }

class DataVal a where
  printData :: a -> String

instance DataVal String where
  printData s =
    let quoted_s = "\"" ++ s ++ "\"" in
      if s == "" || ' ' `elem` s then quoted_s else s

instance DataVal Int where
  printData = show

instance DataVal Float where
  printData = show

instance DataVal Bool where
  printData b = if b then "true" else "false"

kv :: DataVal a => String -> a -> DataValue
kv k v = DataValue k (printData v)

dataHeader :: [DataValue] -> String
dataHeader = intercalate "\t" . map key

dataRow :: [DataValue] -> String
dataRow = intercalate "\t" . map value
