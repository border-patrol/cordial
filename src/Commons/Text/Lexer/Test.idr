module Commons.Text.Lexer.Test

import Text.PrettyPrint.WL
import Text.Lexer

import Commons.Data.Location
import Commons.Text.Lexer.Run


%default total
%access export

data TestReport : Type -> Type where
  ExpectedSuccess : (title : String) -> TestReport a

  Failure : (Eq a, Show a)
         => (title : String)
         -> (input : String)
         -> LexError
         -> TestReport a

  UnexpectedSuccess : (Eq a, Show a)
                   => (title, input : String)
                   -> (given : List (TokenData a))
                   -> TestReport a

  FailureCmp : (Eq a, Show a)
            => (title, input : String)
            -> (given, expected : List (TokenData a))
            -> TestReport a

isSuccess : TestReport a -> Bool
isSuccess (ExpectedSuccess _) = True
isSuccess _ = False

lexerTest : (Eq a, Show a)
         => (title : String)
         -> (lex   : String -> Either LexError (List (TokenData a)))
         -> (input : String)
         -> TestReport a
lexerTest t l i =
  case l i of
    Left err => Failure t i err
    Right ts => ExpectedSuccess t

lexerTestNot : (Eq a, Show a)
            => (title : String)
            -> (lex   : String -> Either LexError (List (TokenData a)))
            -> (input : String)
            -> TestReport a
lexerTestNot t l i =
  case l i of
    Left err => ExpectedSuccess t
    Right ts => UnexpectedSuccess t i ts

lexerTestAssert : (Eq a, Show a)
            => (title : String)
            -> (lex   : String -> Either LexError (List (TokenData a)))
            -> (input : String)
            -> (expected : List (TokenData a))
            -> TestReport a
lexerTestAssert t l i e =
  case l i of
    Right ts =>
      if map tok ts == map tok e
        then ExpectedSuccess t
        else FailureCmp t i ts e

    Left err => Failure t i err


showReport : Show a => TestReport a -> Doc
showReport (ExpectedSuccess t) = text "[PASS]" <+> text t
showReport (Failure t i err) =
  vcat [ text "[FAIL]" <+> text t
       , indent 2 $ text "This input:"
       , indent 4 $ text i
       , indent 2 $ text "gave this error:"
       , indent 4 $ (text . show) err]
showReport (UnexpectedSuccess t i g) =
   vcat [ text "[FAIL] [RESULT]" <+> text t
       , indent 2 $ text "This input:"
       , indent 4 $ text i
       , indent 2 $ text "unexpectedly gave this result:"
       , indent 4 $ list (map (text . show . tok) g)
       ]

showReport (FailureCmp t i g e) =
  vcat [ text "[FAIL]" <+> text t
       , indent 2 $ text "Expected to lex:"
       , indent 4 $ list (map (text . show . tok) e)
       , indent 2 $ text "But gave this:"
       , indent 4 $ list (map (text . show . tok) g)]

runLexTest : Show a => TestReport a -> IO Bool
runLexTest r = do putStrLn ((toString . showReport) r)
                  pure (isSuccess r)
