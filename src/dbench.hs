{-# LANGUAGE Rank2Types, FlexibleContexts #-}
module Dbench where

import Control.Monad (void)
import Data.Maybe (catMaybes)
import Data.Word (Word8)
import Data.Text.Read (hexadecimal)
import qualified Data.Text as T
import Text.Parsec

-- model DBENCH SMB loadfiles

type Path = String

data OffsetExpr =
  ConstantOffset Int
  | Random
  | Align Int OffsetExpr
  | Modulo Int OffsetExpr
  | Add Int OffsetExpr
  deriving (Eq, Show)

data ExpectedStatus = ExpectSuccess | ExpectError | DontCare
  deriving (Eq, Show)

type Flags = Word8

newtype Pattern = Pattern String
  deriving (Eq, Show)

oRDWRCREATE :: Word8
oRDWRCREATE = 0xc

data Command =
  Read Path OffsetExpr Int ExpectedStatus
  | Write Path OffsetExpr Int ExpectedStatus
  | Open Path Flags ExpectedStatus
  | Mkdir Path ExpectedStatus
  | Rmdir Path ExpectedStatus
  | RandomString Int Pattern
  | RepeatNext Int
  deriving (Eq, Show)

type Script = [Command]

-- parse loadfiles

type ParserT a = forall m s.
  Stream s m Char => ParsecT s () m a

constant :: String -> a -> ParserT a
constant s x = string s >> return x

inQuotes :: ParserT String
inQuotes = between (char '"') (char '"') (many (noneOf "\""))

path :: ParserT Path
path = inQuotes

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

offsetTransform :: ParserT (OffsetExpr -> OffsetExpr)
offsetTransform = (do
  t1 <- choice [ char '/' >> Align <$> number
               , char '%' >> Modulo <$> number
               , char '+' >> Add <$> number ]
  t2 <- offsetTransform
  return $ t2 . t1) <|> return id

baseOffset :: ParserT OffsetExpr
baseOffset = choice [ ConstantOffset <$> number
                      , constant "*" Random ]

offset :: ParserT OffsetExpr
offset = do
  off <- baseOffset
  offsetTransform <*> return off

flags :: ParserT Flags
flags = fromIntegral <$> number

expectedStatus :: ParserT ExpectedStatus
expectedStatus = constant "SUCCESS" ExpectSuccess
                 <|> constant "ERROR" ExpectError
                 <|> constant "*" DontCare

whitespace :: ParserT ()
whitespace = void $ many (oneOf " \t")

lexeme :: ParserT a -> ParserT a
lexeme p = p <* whitespace

whitespaceLn :: ParserT ()
whitespaceLn = void $ many (oneOf " \n\t")

lexemeLn :: ParserT a -> ParserT a
lexemeLn p = p <* whitespaceLn

command :: ParserT Command
command = choice (map try (commands ++ others))
          <?> "command"
        where commands =
                map (<*> expectedStatus)
                [ lexeme (string "READ") >>
                  Read <$> lexeme path <*> lexeme offset <*> lexeme number
                , lexeme (string "WRITE") >>
                  Write <$> lexeme path <*> lexeme offset <*> lexeme number
                , lexeme (string "OPEN") >>
                  Open <$> lexeme path <*> lexeme flags
                , lexeme (string "MKDIR") >>
                  Mkdir <$> lexeme path
                , lexeme (string "RMDIR") >>
                  Rmdir <$> lexeme path]
              others =
                [ lexeme (string "RANDOMSTRING") >>
                  RandomString <$> lexeme number <*> lexeme patternP
                , lexeme (string "REPEAT") >>
                  RepeatNext <$> lexeme number]

comment :: ParserT String
comment = char '#' >> manyTill anyChar (try (void (char '\n') <|> eof))

script :: ParserT Script
script = catMaybes <$>
  manyTill (lexemeLn (Just <$> command)
             <|> (comment >> return Nothing)) eof
