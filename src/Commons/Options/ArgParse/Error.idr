-- --------------------------------------------------------------- [ Error.idr ]
-- Module    : Error.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

module Commons.Options.ArgParse.Error

import Commons.Data.Location

import Commons.Options.ArgParse.Model
import Commons.Options.ArgParse.Lexer
import Commons.Options.ArgParse.Parser

%default total
%access public export

data ArgParseError : Type where
  InvalidOption   : Arg -> ArgParseError
  MalformedOption : ParseError Token -> ArgParseError

(Show Arg) => Show ArgParseError where
  show (InvalidOption o) = "Invalid Option " ++ show o
  show (MalformedOption (PError (MkParseFail error location rest))) =
    unlines [show location, error]
  show (MalformedOption (LError (MkLexFail l i)))  = unwords [show l, ":\n" <+> i]
  show (MalformedOption (FError x))  = unlines ["File Error:", show x]


-- --------------------------------------------------------------------- [ EOF ]
