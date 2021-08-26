module Commons.Options.ArgParse.Parser.API

import Data.String.Views

import Text.Token
import Text.Lexer
import Text.Parser

import Commons.Options.ArgParse.Lexer
import public Commons.Text.Parser.Support


%default total
%access export

-- Some basic parsers used by all the intermediate forms

export
shortFlag : Rule Token String
shortFlag
    = terminal  (\x => case tok x of
                           SFlag f => Just (substr 1 (length f) f)
                           _     => Nothing)

export
longFlag : Rule Token String
longFlag
    = terminal (\x => case tok x of
                           LFlag f => Just (substr 2 (length f) f)
                           _       => Nothing)

export
arg : Rule Token String
arg = terminal
  (\x => case tok x of
           Arg s => Just (trim s)
           _     => Nothing)

export
equals : Rule Token ()
equals = terminal
  (\x => case tok x of
           Equals _ => Just ()
           _        => Nothing)

export
quoted : Rule Token String
quoted = terminal
    (\x => case tok x of
             Quoted s => Just $ rmQuotes s
             _        => Nothing)
  where
    rmQuotes : String -> String
    rmQuotes xs = pack $ filter (not . (==) '"') (unpack xs)

-- --------------------------------------------------------------------- [ EOF ]
