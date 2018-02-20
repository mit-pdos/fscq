{-# LANGUAGE Rank2Types, FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
import           Control.Monad.Identity (Identity)
import qualified Data.Text as T
import           DbenchScript
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
      (expectedStatus, "NT_STATUS_OK") `shouldParseTo` StatusOk
      (expectedStatus, "NT_STATUS_OBJECT_NAME_NOT_FOUND") `shouldParseTo` StatusNameNotFound
      (expectedStatus, "NT_STATUS_OBJECT_PATH_NOT_FOUND") `shouldParseTo` StatusPathNotFound
      (expectedStatus, "NT_STATUS_NO_SUCH_FILE") `shouldParseTo` StatusNoSuchFile
  describe "path parser" $ do
    it "should parse normal paths" $ do
      (path, "\"/foo\"") `shouldParseTo` "/foo"
    it "should parse paths with forward slashes" $ do
      (path, "\"\\foo\\bar\"") `shouldParseTo` "/foo/bar"
  describe "command parser" $ do
    it "should parse common operations" $ do
      (command, "NTCreateX \"\\clients\\client1\" 0x1 0x2 16385 NT_STATUS_OK") `shouldParseTo`
        CreateX "/clients/client1" (CreateOptions 0x1) (CreateDisposition 0x2) (Handle 16385) StatusOk
      (command, "WriteX 10002 1835008 32768 32768 NT_STATUS_OK") `shouldParseTo`
        WriteX (Handle 10002) 1835008 32768 32768 StatusOk
      (command, "ReadX 10003 0 4096 4096 NT_STATUS_OK") `shouldParseTo`
        ReadX (Handle 10003) 0 4096 4096 StatusOk
      (command, "QUERY_PATH_INFORMATION \"\\PPTB1E4.TMP\" 1004 NT_STATUS_OK") `shouldParseTo`
        QueryPath "/PPTB1E4.TMP" 1004 StatusOk
    it "should parse other operations" $ do
      (command, "Close 10003 NT_STATUS_OK") `shouldParseTo`
        Close (Handle 10003) StatusOk
      (command, "FIND_FIRST \"\\clients\\client1\\~dmtmp\\<.JNK\" 260 1366 0 NT_STATUS_NO_SUCH_FILE") `shouldParseTo`
        FindFirst (Pattern "\\clients\\client1\\~dmtmp\\<.JNK") 260 1366 0 StatusNoSuchFile
      (command, "Unlink \"\\clients\\client1\\~dmtmp\\PWRPNT\\NEWPCB.PPT\" 0x6 NT_STATUS_OK") `shouldParseTo`
        Unlink "/clients/client1/~dmtmp/PWRPNT/NEWPCB.PPT" 0x6 StatusOk
      (command, "QUERY_FS_INFORMATION 259 NT_STATUS_OK") `shouldParseTo`
        QueryFilesystem 259 StatusOk
      (command, "QUERY_FILE_INFORMATION 9938 258 NT_STATUS_OK") `shouldParseTo`
        QueryFile (Handle 9938) 258 StatusOk
      (command, "SET_FILE_INFORMATION 10017 1004 NT_STATUS_OK") `shouldParseTo`
        SetFileInfo (Handle 10017) 1004 StatusOk
      (command, "Flush 10024 NT_STATUS_OK") `shouldParseTo`
        Flush (Handle 10024) StatusOk
      (command, "Rename \"\\clients\\client1\\~dmtmp\\PWRPNT\\NEWPCB.PPT\" \"\\clients\\client1\\~dmtmp\\PWRPNT\\PPTC112.TMP\" NT_STATUS_OK") `shouldParseTo`
        Rename "/clients/client1/~dmtmp/PWRPNT/NEWPCB.PPT" "/clients/client1/~dmtmp/PWRPNT/PPTC112.TMP" StatusOk
      (command, "LockX 10430 2147483538 1 NT_STATUS_OK") `shouldParseTo`
        LockX (Handle 10430) 2147483538 1 StatusOk
      (command, "UnlockX 10430 2147483538 1 NT_STATUS_OK") `shouldParseTo`
        UnlockX (Handle 10430) 2147483538 1 StatusOk
      (command, "Mkdir \"\\clients\" NT_STATUS_OK") `shouldParseTo`
        Mkdir "/clients" StatusOk
      (command, "Deltree \"\\clients\\client1\" NT_STATUS_OK") `shouldParseTo`
        Deltree "/clients/client1" StatusOk
    it "should handle whitespace" $ do
      (command, "Close  10003  \tNT_STATUS_OK") `shouldParseTo`
        Close (Handle 10003) StatusOk
    it "internal newlines should not be allowed" $ do
      command `shouldNotParse` "WriteX 100002 12 \n 1 2 NT_STATUS_OK"
  describe "loadfile parser" $ do
    it "should parse two commands" $ do
      (script, T.unlines
        ["Mkdir \"\\clients\" NT_STATUS_OK"
        , "NTCreateX \"\\clients\\f\" 0x1 0x2 12 NT_STATUS_OK"]) `shouldParseTo`
        [Mkdir "/clients" StatusOk
        , CreateX "/clients/f" (CreateOptions 0x1) (CreateDisposition 0x2) (Handle 12) StatusOk]
    it "should skip comments" $ do
      (script, T.unlines
        ["Mkdir \"\\clients\" NT_STATUS_OK"
        , "# this is just a comment"
        , "NTCreateX \"\\clients\\f\" 0x1 0x2 12 NT_STATUS_OK"]) `shouldParseTo`
        [Mkdir "/clients" StatusOk
        , CreateX "/clients/f" (CreateOptions 0x1) (CreateDisposition 0x2) (Handle 12) StatusOk]
