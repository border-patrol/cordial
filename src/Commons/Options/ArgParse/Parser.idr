-- -------------------------------------------------------------- [ Parser.idr ]
-- Description : A simple parser for command options.
-- Copyright   : (c) Jan de Muijnck-Hughes
-- License     : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
module Commons.Options.ArgParse.Parser

import Text.Lexer
import Text.Parser

import Commons.Text.Lexer.Run
import public Commons.Text.Parser.Run

import Commons.Options.ArgParse.Lexer
import Commons.Options.ArgParse.Parser.API
import Commons.Options.ArgParse.Model

%access private

-- ----------------------------------------------------------------- [ Parsers ]

flagLong : Rule Token Arg
flagLong = do
  l <- longFlag
  pure $ Flag l

flagShort : Rule Token Arg
flagShort = do
   s <- shortFlag
   pure $ Flag s

kvLong : Rule Token Arg
kvLong = do
    key <- longFlag
    equals
    value <- (arg <|> quoted)
    pure $ KeyValue key value

kvShort : Rule Token Arg
kvShort = do
    k <- shortFlag
    v <- (arg <|> quoted)
    pure $ KeyValue k v

options : Rule Token Arg
options = kvShort <|> kvLong <|> flagShort <|> flagLong <|> (do fs <- arg; pure $ File fs)

args : RuleEmpty Token $ List Arg
args = do
    os <- many options
    pure $ os

export
parseArgsStr : (str  : String)
            -> Either (Run.ParseError Token) (List Arg)
parseArgsStr str = parseString ArgParseLexer args str

export
parseArgsFile :(fname : String)
            -> IO (Either (Run.ParseError Token) (List Arg))
parseArgsFile fn = parseFile ArgParseLexer args fn

-- --------------------------------------------------------------------- [ EOF ]
