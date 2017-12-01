{-# LANGUAGE Rank2Types, FlexibleContexts #-}
{-# LANGUAGE DataKinds, KindSignatures, GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
module Dbench where

import           Control.Monad (void)
import qualified Control.Monad.State.Strict as S
import           Data.Int (Int64)
import           Data.Maybe (catMaybes)
import qualified Data.Text as T
import           Data.Text.Read (hexadecimal)
import           Data.Word (Word8)
import qualified System.Random as Random
import           Text.Parsec

-- model DBENCH SMB loadfiles

type Path = String

data Phase = Meta | Processed

data OffsetExpr :: Phase -> * where
  ConstantOffset :: Int -> OffsetExpr p
  Random :: OffsetExpr 'Meta
  Align :: Int -> OffsetExpr 'Meta -> OffsetExpr 'Meta
  Modulo :: Int -> OffsetExpr 'Meta -> OffsetExpr 'Meta
  Add :: Int -> OffsetExpr 'Meta -> OffsetExpr 'Meta

deriving instance Eq (OffsetExpr p)
deriving instance Show (OffsetExpr p)

data ExpectedStatus = ExpectSuccess | ExpectError | DontCare
  deriving (Eq, Show)

type Flags = Word8

newtype Pattern = Pattern String
  deriving (Eq, Show)

oRDWRCREATE :: Word8
oRDWRCREATE = 0xc

data Command :: Phase -> * where
  Read :: Path -> OffsetExpr p -> Int -> ExpectedStatus -> Command p
  Write :: Path -> OffsetExpr p -> Int -> ExpectedStatus -> Command p
  Open :: Path -> Flags -> ExpectedStatus -> Command p
  Mkdir :: Path -> ExpectedStatus -> Command p
  Rmdir :: Path -> ExpectedStatus -> Command p
  RandomString :: Int -> Pattern -> Command 'Meta
  Repeat :: Int -> Command 'Meta -> Command 'Meta

deriving instance Eq (Command p)
deriving instance Show (Command p)

type Script p = [Command p]

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

offsetTransform :: ParserT (OffsetExpr 'Meta -> OffsetExpr 'Meta)
offsetTransform = (do
  t1 <- choice [ char '/' >> Align <$> number
               , char '%' >> Modulo <$> number
               , char '+' >> Add <$> number ]
  t2 <- offsetTransform
  return $ t2 . t1) <|> return id

baseOffset :: ParserT (OffsetExpr 'Meta)
baseOffset = choice [ ConstantOffset <$> number
                      , constant "*" Random ]

offset :: ParserT (OffsetExpr 'Meta)
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

newlineOrEof :: ParserT ()
newlineOrEof = try (void (char '\n')) <|> eof

whitespaceLn :: ParserT ()
whitespaceLn = void $ manyTill (oneOf " \t") newlineOrEof

lexemeLn :: ParserT a -> ParserT a
lexemeLn p = p <* whitespaceLn

command :: ParserT (Command 'Meta)
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
                  Repeat <$> lexemeLn number <*> command]

comment :: ParserT String
comment = char '#' >> manyTill anyChar newlineOrEof

script :: ParserT (Script 'Meta)
script = catMaybes <$>
  manyTill (lexemeLn (Just <$> command)
             <|> (comment >> return Nothing)) eof

-- lowering commands to be processed

type RandomM a = S.State Random.StdGen a

random :: Random.Random a => RandomM a
random = S.state Random.random

getOffset :: OffsetExpr 'Processed -> Int
getOffset (ConstantOffset off) = off

evalOffset :: OffsetExpr 'Meta -> RandomM (OffsetExpr 'Processed)
evalOffset = eval
  where eval :: OffsetExpr 'Meta -> RandomM (OffsetExpr 'Processed)
        eval (ConstantOffset off) = return $ ConstantOffset off
        eval Random = ConstantOffset . fromIntegral <$> (random :: RandomM Int64)
        eval (Align n e) = do
          off <- getOffset <$> eval e
          return $ ConstantOffset (off `div` n * n)
        eval (Modulo n e) = do
          off <- getOffset <$> eval e
          return $ ConstantOffset (off `mod` n)
        eval (Add n e) = do
          off <- getOffset <$> eval e
          return $ ConstantOffset (off + n)

evalCommand :: Command 'Meta -> [RandomM (Command 'Processed)]
evalCommand = eval
  where singleton x = [x]
        eval :: Command 'Meta -> [RandomM (Command 'Processed)]
        eval (Read p off len s) = singleton $ do
          off' <- evalOffset off
          return $ Read p off' len s
        eval (Write p off len s) = singleton $ do
          off' <- evalOffset off
          return $ Write p off' len s
        eval (Open p f s) = singleton $ return $ Open p f s
        eval (Mkdir p s) = singleton $ return $ Mkdir p s
        eval (Rmdir p s) = singleton $ return $ Rmdir p s
        eval (RandomString _ (Pattern _)) = [] -- TODO: generate and store a random string somewhere
        eval (Repeat n c) = concat $ replicate n (eval c)

evalScript :: Script 'Meta -> RandomM (Script 'Processed)
evalScript s = sequence $ concatMap evalCommand s
