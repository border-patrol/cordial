module Commons.Test.Unit.Lexer

import Text.PrettyPrint.WL

import Text.Lexer

%default total
%access export

data TestReport : Type -> Type where
  ExpectedSuccess : (title : String) -> TestReport a

  Failure : (Eq a, Show a)
         => (title : String)
         -> (input : String)
         -> (lexed : List (TokenData a))
         -> (left  : String)
         -> TestReport a

  FailureCmp : (Eq a, Show a)
            => (title, input : String)
            -> (given, expected : List (TokenData a))
            -> TestReport a

isSuccess : TestReport a -> Bool
isSuccess (ExpectedSuccess _) = True
isSuccess _ = False

data LexResult a = Empty Int Int String
                 | Success (List (TokenData a)) Int Int
                 | Extra   (List (TokenData a)) Int Int String

lexFunc : {a : Type}
       -> (Eq a, Show a)
       => (String -> Pair (List (TokenData a)) (Int, Int, String))
       -> String
       -> LexResult a
lexFunc l i = case l i of
                (Nil, (l,c,str)) => Empty l c str
                (ts , (l,c,""))  => Success ts l c
                (ts , (l,c,str)) => Extra ts l c str

lexerTest : (Eq a, Show a)
         => (title : String)
         -> (lex   : String -> Pair (List (TokenData a)) (Int, Int, String))
         -> (input : String)
         -> TestReport a
lexerTest t l i {a} =
  case lexFunc {a=a} l i of
    Empty _ _ str => Failure t i Nil str
    Success ts _ _ => ExpectedSuccess t
    Extra ts _ _ str => Failure t i ts str

lexerTestNot : (Eq a, Show a)
            => (title : String)
            -> (lex   : String -> Pair (List (TokenData a)) (Int, Int, String))
            -> (input : String)
            -> TestReport a
lexerTestNot t l i =
  case lexFunc l i of
    Success ts _ _ => Failure t i ts ""
    Extra ts _ _ str => Failure t i ts str
    Empty _ _ str => ExpectedSuccess t

lexerTestAssert : (Eq a, Show a)
            => (title : String)
            -> (lex   : String -> Pair (List (TokenData a)) (Int, Int, String))
            -> (input : String)
            -> (expected : List (TokenData a))
            -> TestReport a
lexerTestAssert t l i e =
  case lexFunc l i of
    Success ts _ _ =>
      if map tok ts == map tok e
        then ExpectedSuccess t
        else FailureCmp t i ts e

    Empty _ _ str => Failure t i Nil str
    Extra ts _ _ str => Failure t i ts str

showReport : Show a => TestReport a -> Doc
showReport (ExpectedSuccess t) = text "[PASS]" <+> text t
showReport (Failure t i sofar left) =
  vcat [ text "[FAIL]" <+> text t
       , indent 2 $ text "So far I lexed:"
       , indent 4 $ list (map (text . show . tok) sofar)
       , indent 2 $ text "This was left:"
       , indent 4 $ text left]
showReport (FailureCmp t i g e) =
  vcat [ text "[FAIL]" <+> text t
       , indent 2 $ text "Expected to lex:"
       , indent 4 $ list (map (text . show . tok) e)
       , indent 2 $ text "But gave this:"
       , indent 4 $ list (map (text . show . tok) g)]

runLexTest : Show a => TestReport a -> IO Bool
runLexTest r = do putStrLn ((toString . showReport) r)
                  pure (isSuccess r)
