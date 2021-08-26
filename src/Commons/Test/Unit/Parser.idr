module Commons.Test.Unit.Parser

import Text.PrettyPrint.WL

import Text.Lexer
import Text.Parser

%default total
%access export

data TestReport : Type where
  ExpectedSuccess : (title : String) -> TestReport

  Failure : (title, msg : String) -> TestReport

  UnexpectedSuccess : (Show a)
                   => (title : String)
                   -> (made  : a)
                   -> TestReport

  FailureCmp : (Eq a, Show a)
            => (title, input : String)
            -> (expected : a)
            -> (given : a)
            -> TestReport

  WrongError : Show e
            => (title, input : String)
            -> (expected : e)
            -> (given    : e)
            -> TestReport

isSuccess : TestReport -> Bool
isSuccess (ExpectedSuccess _) = True
isSuccess _ = False

parseTest : Show tok
         => (title : String)
         -> (p : String -> Either (ParseError tok) ty)
         -> String
         -> TestReport
parseTest t run i =
  case run i of
    Left (Error err _) => Failure t err
    Right _ => ExpectedSuccess t

parseFail : Show ty
         => (title : String)
         -> (p : String -> Either (ParseError tok) (ty))
         -> String
         -> TestReport
parseFail t run i =
  case run i of
    Left _ => ExpectedSuccess t
    Right (res) => UnexpectedSuccess t res

parseTestAssert : (Eq ty, Show ty)
               => (title : String)
               -> (p : String -> Either (ParseError tok) (ty))
               -> String
               -> ty
               -> (ty -> ty -> Bool)
               -> TestReport
parseTestAssert t run i exp eq =
  case run i of
    Left (Error err _) => Failure t err
    Right (given) =>
      if eq given exp
        then ExpectedSuccess t
        else FailureCmp t i exp given

parseTestError : Show ty
               => (title : String)
               -> (p : String -> Either (ParseError tok) (ty))
               -> String
               -> String
               -> TestReport
parseTestError t run i exp =
  case run i of
    Left (Error err _ ) =>
      if (trim err) == (trim exp)
        then ExpectedSuccess t
        else WrongError t i exp err
    Right (res) => UnexpectedSuccess t res


showReport : TestReport-> Doc
showReport (ExpectedSuccess t) =  text "[PASS]" <+> text t
showReport (Failure t m) =
  vcat [ text "[FAIL] [PARSING]" <+> text t
       , indent 2 $ text "Gave error:"
       , text m
       ]
showReport (UnexpectedSuccess t res) =
  vcat [ text "[FAIL] [RESULT]" <+> text t
       , indent 2 $ text "Unexpectedly made:"
       , indent 4 $ (text . show) res
       ]
showReport (FailureCmp t i e g) =
  vcat [ text "[FAIL] [PARSING]" <+> text t
       , indent 2 $ text "Given input:"
       , indent 4 (text i)
       , indent 2 $ (text "Should have made:")
       , indent 4 $ (text . show) e
       , indent 2 $ (text "but made:")
       , indent 4 $ (text . show) g
       ]
showReport (WrongError t i e g) =
  vcat [ text "[FAIL] [ERROR]" <+> text t
       , indent 2 $ text "Given input:"
       , indent 4 (text i)
       , indent 2 $ (text "Should have errored with:")
       , indent 4 $ (text . show) e
       , indent 2 $ (text "but error was:")
       , indent 4 $ (text . show) g
       ]

runParseTest : Show a => TestReport -> IO Bool
runParseTest r = do putStrLn ((toString . showReport) r)
                    pure (isSuccess r)
