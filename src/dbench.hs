{-# LANGUAGE Rank2Types, FlexibleContexts #-}
{-# LANGUAGE DataKinds, KindSignatures, GADTs #-}
{-# LANGUAGE FlexibleInstances, StandaloneDeriving #-}
module Dbench where

import           Control.Monad (void, replicateM)
import qualified Control.Monad.State.Strict as S
import           Data.Char (digitToInt)
import           Data.Int (Int64)
import           Data.Maybe (catMaybes)
import           Data.String
import qualified Data.Text as T
import           Data.Text.Read (hexadecimal)
import           Data.Word (Word8)
import qualified System.Random as Random
import           Text.Parsec

-- model DBENCH SMB loadfiles

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

data PathComponent :: Phase -> * where
  CPath :: String -> PathComponent p
  Reference :: Int -> PathComponent 'Meta

deriving instance Eq (PathComponent p)
deriving instance Show (PathComponent p)

newtype Path p = Path [PathComponent p]
  deriving (Eq, Show)

instance IsString (Path 'Meta) where
  fromString s = Path [CPath s]

data PatternComponent =
  CPattern String
  | AnyChar String
  deriving (Eq, Show)

newtype Pattern = Pattern [PatternComponent]
  deriving (Eq, Show)

instance IsString Pattern where
  fromString s = Pattern [CPattern s]

oRDWRCREATE :: Word8
oRDWRCREATE = 0xc

data Command :: Phase -> * where
  Read :: Path p -> OffsetExpr p -> Int -> ExpectedStatus -> Command p
  Write :: Path p -> OffsetExpr p -> Int -> ExpectedStatus -> Command p
  Open :: Path p -> Flags -> ExpectedStatus -> Command p
  Mkdir :: Path p -> ExpectedStatus -> Command p
  Rmdir :: Path p -> ExpectedStatus -> Command p
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

patternsEndBy :: ParserT a -> (String -> a) -> ParserT end -> ParserT [a]
patternsEndBy pat normal end = manyTill component end
  where checkPattern = try . lookAhead $ void pat <|> void end
        component = pat
          <|> (normal <$> manyTill anyChar checkPattern)

reference :: ParserT (PathComponent 'Meta)
reference = char '$' >> (Reference . digitToInt <$> digit)

path :: ParserT (Path 'Meta)
path = Path <$> (char '"' >> patternsEndBy reference CPath (char '"'))

charSet :: ParserT PatternComponent
charSet = AnyChar <$> between (char '[') (char ']') (many (noneOf "]"))

patternP :: ParserT Pattern
patternP = do
  comps <- char '"' >> patternsEndBy charSet CPattern (char '"')
  let p = if null comps then [CPattern ""] else comps in
    return $ Pattern p

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

-- a convenient randomness monad, wrapping StdGen
-- (not generalized over generators due to lack of impredicative polymorphism)
type RandomM a = S.State Random.StdGen a

random :: Random.Random a => RandomM a
random = S.state Random.random

runRandom :: RandomM a -> IO a
runRandom x = S.evalState x <$> Random.getStdGen

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

evalPath :: Path 'Meta -> Path 'Processed
evalPath (Path p) = Path (eval p)
  where eval :: [PathComponent 'Meta] -> [PathComponent 'Processed]
        eval (CPath s:p') = CPath s:eval p'
        eval (Reference _:_) = error "references in paths are unimplemented"
        eval [] = []

randomChar :: String -> RandomM Char
randomChar s = do
  off <- S.state $ Random.randomR (0, length s-1)
  return $ s !! off

evalPatternComponent :: PatternComponent -> RandomM String
evalPatternComponent = eval
  where eval :: PatternComponent -> RandomM String
        eval (CPattern s) = return s
        eval (AnyChar cs) = do
          c <- randomChar cs
          return [c]

evalPattern :: Pattern -> RandomM String
evalPattern (Pattern ps) = concat <$> mapM evalPatternComponent ps

evalCommand :: Command 'Meta -> RandomM [Command 'Processed]
evalCommand = eval
  where singleton x = [x]
        eval :: Command 'Meta -> RandomM [Command 'Processed]
        eval (Read p off len s) = do
          off' <- evalOffset off
          return . singleton $ Read (evalPath p) off' len s
        eval (Write p off len s) = do
          off' <- evalOffset off
          return . singleton $ Write (evalPath p) off' len s
        eval (Open p f s) =
          return . singleton $ Open (evalPath p) f s
        eval (Mkdir p s) =
          return . singleton $ Mkdir (evalPath p) s
        eval (Rmdir p s) =
          return . singleton $ Rmdir (evalPath p) s
        eval (RandomString _ (Pattern _)) = return [] -- TODO: generate and store a random string somewhere
        eval (Repeat n c) =
          concat <$> replicateM n (eval c)

evalScript :: Script 'Meta -> RandomM (Script 'Processed)
evalScript s = concat <$> mapM evalCommand s
