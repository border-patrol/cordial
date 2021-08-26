module Commons.Test.Unit.Parser

import Text.PrettyPrint.WL

import Text.Lexer
import Text.Parser

import Commons.Data.Location

import Commons.Text.Lexer.Run
import Commons.Text.Parser.Run

%default total
%access export

data TestReport : Type -> Type where
  ExpectedSuccess : (title : String) -> TestReport tok

  Failure : Show a => (title : String) -> (Run.ParseError a) -> TestReport a

  UnexpectedSuccess : (Show a)
                   => (title : String)
                   -> (made  : a)
                   -> TestReport tok

  FailureCmp : (Eq a, Show a)
            => (title, input : String)
            -> (expected : a)
            -> (given : a)
            -> TestReport tok

isSuccess : TestReport e -> Bool
isSuccess (ExpectedSuccess _) = True
isSuccess _ = False

parseTest : Show tok
         => (title : String)
         -> (p : String -> Either (Run.ParseError tok) ty)
         -> String
         -> TestReport tok
parseTest t run i =
  case run i of
    Left err => Failure t err
    Right _ => ExpectedSuccess t

parseFail : Show ty
         => (title : String)
         -> (p : String -> Either (Run.ParseError tok) (ty))
         -> String
         -> TestReport tok
parseFail t run i =
  case run i of
    Left _ => ExpectedSuccess t
    Right (res) => UnexpectedSuccess t res

parseTestAssert : (Show tok, Eq ty, Show ty)
               => (title : String)
               -> (p : String -> Either (Run.ParseError tok) (ty))
               -> String
               -> ty
               -> (ty -> ty -> Bool)
               -> TestReport tok
parseTestAssert t run i exp eq =
  case run i of
    Left err => Failure t err
    Right (given) =>
      if eq given exp
        then ExpectedSuccess t
        else FailureCmp t i exp given

showReport : (Run.ParseError tok -> String) -> TestReport tok -> Doc
showReport f (ExpectedSuccess t) =  text "[PASS]" <+> text t
showReport f (Failure t m) =
  vcat [ text "[FAIL] [PARSING]" <+> text t
       , indent 2 $ text "Gave error:"
       , indent 4 $ text (f m)
       ]
showReport f (UnexpectedSuccess t res) =
  vcat [ text "[FAIL] [RESULT]" <+> text t
       , indent 2 $ text "Unexpectedly made:"
       , indent 4 $ (text . show) res
       ]
showReport f (FailureCmp t i e g) =
  vcat [ text "[FAIL] [PARSING]" <+> text t
       , indent 2 $ text "Given input:"
       , indent 4 (text i)
       , indent 2 $ (text "Should have made:")
       , indent 4 $ (text . show) e
       , indent 2 $ (text "but made:")
       , indent 4 $ (text . show) g
       ]

runParseTest : Show tok => (Run.ParseError tok -> String) -> TestReport tok -> IO Bool
runParseTest f r = do putStrLn ((toString . showReport f) r)
                      pure (isSuccess r)
