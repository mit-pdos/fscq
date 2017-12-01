{-# LANGUAGE Rank2Types, FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
import           Control.Monad.Identity (Identity)
import qualified Data.Text as T
import           Dbench
import           Test.Hspec
import           Text.Parsec

{-# ANN module ("HLint: ignore Redundant do" :: String) #-}

shouldParseTo
  :: (Show a, Eq a)
  => (ParsecT T.Text () Identity a, T.Text)
  -> a -> Expectation
shouldParseTo (p, s) x =
  runParser p () "" s `shouldBe` Right x

shouldNotParse
  :: (Show a)
  => ParserT a -> String -> Expectation
shouldNotParse p s =
  runParser p () "" s `shouldSatisfy` \r ->
  case r of
    Left _ -> True
    Right _ -> False

main :: IO ()
main = hspec $ do
  describe "low-level parsers" $ do
    it "number should parse decimals" $ do
      (number, "12") `shouldParseTo` 12
      (number, "09") `shouldParseTo` 9
    it "number should parse hex" $ do
      (number, "0x10") `shouldParseTo` 16
      (number, "0xfc") `shouldParseTo` 0xfc
    it "flags should parse hex" $ do
      (flags, "0xc") `shouldParseTo` 0xc
    it "whitespace parser should be greedy" $ do
      (whitespace >> eof, "  \t") `shouldParseTo` ()
    it "status constants should parse" $ do
      (expectedStatus, "SUCCESS") `shouldParseTo` ExpectSuccess
      (expectedStatus, "ERROR") `shouldParseTo` ExpectError
      (expectedStatus, "*") `shouldParseTo` DontCare
  describe "offset parser" $ do
    it "base offset should parse numbers" $ do
      (baseOffset, "0x1000") `shouldParseTo` ConstantOffset 0x1000
    it "base offset should parse random token" $ do
      (baseOffset, "*") `shouldParseTo` Random
    it "offset transform should parse alignment" $ do
      (offsetTransform <*> return Random, "/10") `shouldParseTo` Align 10 Random
    it "offset transform should parse add" $ do
      (offsetTransform <*> return Random, "+0x10") `shouldParseTo` Add 0x10 Random
    it "offset should parse single modifications" $ do
      (offset, "*/10") `shouldParseTo` Align 10 Random
    it "offset should parse multiple modifications" $ do
      (offset, "*/10+1") `shouldParseTo` Add 1 (Align 10 Random)
    it "offset should parse all modifications" $ do
      (offset, "*/10+1%2") `shouldParseTo` Modulo 2 (Add 1 (Align 10 Random))
    it "offset should parse modifications of constants" $ do
      (offset, "0x13/10") `shouldParseTo` Align 10 (ConstantOffset 0x13)
  describe "command parser" $ do
    it "should parse operations" $ do
      (command, "READ \"/foo\" * 1024 *") `shouldParseTo` Read "/foo" Random 1024 DontCare
      (command, "WRITE \"/foo\" * 1024 ERROR") `shouldParseTo` Write "/foo" Random 1024 ExpectError
      (command, "OPEN \"/here/there\" 0xc SUCCESS") `shouldParseTo` Open "/here/there" 0xc ExpectSuccess
      (command, "MKDIR \"/here/there\" SUCCESS") `shouldParseTo` Mkdir "/here/there" ExpectSuccess
      (command, "RMDIR \"/here/there\" SUCCESS") `shouldParseTo` Rmdir "/here/there" ExpectSuccess
    it "should parse control commands" $ do
      (command, "RANDOMSTRING 1 \"file[01].dat\"") `shouldParseTo` RandomString 1 (Pattern "file[01].dat")
      (command, "REPEAT 10\nREAD \"/foo\" * 1024 *") `shouldParseTo` Repeat 10 (Read "/foo" Random 1024 DontCare)
    it "should not parse repeat in isolation" $ do
      command `shouldNotParse` "REPEAT 10"
    it "should handle whitespace" $ do
      (command, "READ \"/foo\"  \t*   1024 *\t") `shouldParseTo` Read "/foo" Random 1024 DontCare
    it "internal newlines should not be allowed" $ do
      command `shouldNotParse` "WRITE \"/foo\" * \n 1024 ERROR"
  describe "loadfile parser" $ do
    it "should parse two commands" $ do
      (script, T.unlines
        ["RANDOMSTRING 1 \"\""
        , "READ \"/f\" * 1 *"]) `shouldParseTo`
        [RandomString 1 (Pattern ""), Read "/f" Random 1 DontCare]
    it "should skip comments" $ do
      (script, T.unlines
        ["RANDOMSTRING 1 \"\""
        , "# this is just a comment"
        , "READ \"/f\" * 1 *"]) `shouldParseTo`
        [RandomString 1 (Pattern ""), Read "/f" Random 1 DontCare]
