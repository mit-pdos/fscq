{-# LANGUAGE Rank2Types, FlexibleContexts #-}
module DbenchScript where

import           Control.Monad (void)
import           Data.Bits (testBit)
import           Data.Maybe (catMaybes)
import           Data.String (IsString(..))
import qualified Data.Text as T
import qualified Data.Text.IO as T
import           Data.Text.Read (hexadecimal)
import           Data.Word (Word8)
import           Text.Parsec

-- model DBENCH fileio loadfiles

data ExpectedStatus = StatusOk | StatusNameNotFound | StatusPathNotFound | StatusNoSuchFile
  deriving (Eq, Show)

type Offset = Int
type Flags = Word8

newtype Path = Path FilePath
  deriving (Eq, Show)
newtype Handle = Handle Int
  deriving (Eq, Show, Ord)

instance IsString Path where
  fromString = Path

newtype CreateOptions = CreateOptions Flags
  deriving (Eq, Show)

isCreate :: CreateDisposition -> Bool
isCreate (CreateDisposition f) =
  -- FILE_CREATE
  f == 2

isOverwriteFile :: CreateDisposition -> Bool
isOverwriteFile (CreateDisposition f) =
  -- FILE_OVERWRITE
  f == 4 ||
  -- FILE_OVERWRITE_IF
  f == 5

newtype CreateDisposition = CreateDisposition Flags
  deriving (Eq, Show)

hasFileDirectoryFile :: CreateOptions -> Bool
hasFileDirectoryFile (CreateOptions f) = testBit f 0

newtype Pattern = Pattern FilePath
  deriving (Eq, Show)

instance IsString Pattern where
  fromString = Pattern

type MaxCount = Int

data Command =
  CreateX Path CreateOptions CreateDisposition Handle ExpectedStatus
  | ReadX Handle Offset Int Int ExpectedStatus
  | WriteX Handle Offset Int Int ExpectedStatus
  | Close Handle ExpectedStatus
  | QueryPath Path Int ExpectedStatus
  | QueryFile Handle Int ExpectedStatus
  | Unlink Path Int ExpectedStatus
  | FindFirst Pattern Int MaxCount Int ExpectedStatus
  | SetFileInfo Handle Int ExpectedStatus
  | Flush Handle ExpectedStatus
  | Rename Path Path ExpectedStatus
  | LockX Handle Offset Int ExpectedStatus
  | UnlockX Handle Offset Int ExpectedStatus
  | Mkdir Path ExpectedStatus
  | Deltree Path ExpectedStatus
  | QueryFilesystem Int ExpectedStatus
  deriving (Eq, Show)

type Script = [Command]

-- parse loadfiles

type ParserT a = forall m s.
  Stream s m Char => ParsecT s () m a

constant :: String -> a -> ParserT a
constant s x = string s >> return x

inQuotes :: ParserT String
inQuotes = between (char '"') (char '"') (many (satisfy (/= '"')))

replaceBackslashes :: String -> String
replaceBackslashes = map (\c -> if c == '\\' then '/' else c)

path :: ParserT Path
path = Path . replaceBackslashes <$> inQuotes

patternP :: ParserT Pattern
patternP = Pattern <$> inQuotes

hexNumber :: ParserT Int
hexNumber = do
  _ <- string "0x"
  s <- many hexDigit
  case hexadecimal (T.pack s) of
    Right (n, _) -> return n
    _ -> unexpected "could not parse hex constant"

decNumber :: ParserT Int
decNumber = do
  s <- many1 digit
  return $ read s

number :: ParserT Int
number = try hexNumber <|> decNumber <?> "number"

offset :: ParserT Offset
offset = number

flags :: ParserT Flags
flags = fromIntegral <$> number

handle :: ParserT Handle
handle = Handle <$> decNumber

level :: ParserT Int
level = decNumber

expectedStatus :: ParserT ExpectedStatus
expectedStatus = choice . map try $
   [ constant "NT_STATUS_OK" StatusOk
   , constant "NT_STATUS_OBJECT_NAME_NOT_FOUND" StatusNameNotFound
   , constant "NT_STATUS_OBJECT_PATH_NOT_FOUND" StatusPathNotFound
   , constant "NT_STATUS_NO_SUCH_FILE" StatusNoSuchFile ]

whitespace :: ParserT ()
whitespace = void $ many (satisfy (\c -> c == ' ' || c == '\t'))

lexeme :: ParserT a -> ParserT a
lexeme p = p <* whitespace

newlineOrEof :: ParserT ()
newlineOrEof = try (void (char '\n')) <|> eof

whitespaceLn :: ParserT ()
whitespaceLn = void $ manyTill (oneOf " \t") newlineOrEof

lexemeLn :: ParserT a -> ParserT a
lexemeLn p = p <* whitespaceLn

command :: ParserT Command
command = choice (map try commands)
          <?> "command"
        where named s p = lexeme (string s) >> p
              commands =
                map (<*> expectedStatus)
                [
                  named "NTCreateX" $
                  CreateX <$> lexeme path <*> (CreateOptions <$> lexeme flags)
                  <*> (CreateDisposition <$> lexeme flags) <*> lexeme handle
                , named "ReadX" $
                  ReadX <$> lexeme handle <*> lexeme offset <*> lexeme number <*> lexeme number
                , named "WriteX" $
                  WriteX <$> lexeme handle <*> lexeme offset <*> lexeme number <*> lexeme number
                , named "QUERY_PATH_INFORMATION" $
                  QueryPath <$> lexeme path <*> lexeme number
                , named "Close" $
                  Close <$> lexeme handle
                , named "FIND_FIRST" $
                  FindFirst <$> lexeme patternP <*> lexeme level <*> lexeme number <*> lexeme number
                , named "Unlink" $
                  Unlink <$> lexeme path <*> lexeme number
                , named "QUERY_FS_INFORMATION" $
                  QueryFilesystem <$> lexeme level
                , named "QUERY_FILE_INFORMATION" $
                  QueryFile <$> lexeme handle <*> lexeme level
                , named "SET_FILE_INFORMATION" $
                SetFileInfo <$> lexeme handle <*> lexeme level
                , named "Flush" $
                  Flush <$> lexeme handle
                , named "Rename" $
                  Rename <$> lexeme path <*> lexeme path
                , named "LockX" $
                  LockX <$> lexeme handle <*> lexeme number <*> lexeme number
                , named "LockX" $
                  LockX <$> lexeme handle <*> lexeme number <*> lexeme number
                , named "UnlockX" $
                  UnlockX <$> lexeme handle <*> lexeme number <*> lexeme number
                , named "Mkdir" $
                  Mkdir <$> lexeme path
                , named "Deltree" $
                  Deltree <$> lexeme path
                , named "Mkdir" $
                  Mkdir <$> lexeme path]

comment :: ParserT String
comment = char '#' >> manyTill anyChar newlineOrEof

script :: ParserT Script
script = catMaybes <$>
  manyTill (lexemeLn (Just <$> command)
             <|> (comment >> return Nothing)) eof

parseScript :: String -> T.Text -> Either ParseError Script
parseScript = runParser script ()

parseScriptFile :: String -> IO (Either String Script)
parseScriptFile p = do
  t <- T.readFile p
  case parseScript p t of
    Left e -> return $ Left (show e)
    Right s -> return $ Right s
