-- -------------------------------------------------------------- [ Common.idr ]
-- Module    : Common.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

module Text.Markup.Edda.Reader.Common

import public Lightyear
import public Lightyear.Char
import public Lightyear.Strings
import public Lightyear.StringFile

import Effects
import Effect.File
import Effect.StdIO

import Data.AVL.Dict

import Text.Markup.Edda.Model.Common
import Text.Markup.Edda.Model.Raw
import Text.Markup.Edda.Model.Processed

import Text.Markup.Edda.Process

import Text.Markup.Edda.Reader.Utils

%access export

-- ------------------------------------------------------------------ [ Reader ]

readEddaFileE : Parser (EddaRaw DOC)
             -> String
             -> Eff (Either String (Edda DOC)) [FILE ()]
readEddaFileE p f = do
    c <- parseFile (\x,y => unwords [x,show y]) (\x,y => unwords [x,y]) p f
    case  c of
      Left err  => pure $ Left err
      Right res => pure $ Right (processDoc res)

readEddaFile : Parser (EddaRaw DOC)
            -> String
            -> IO (Either String (Edda DOC))
readEddaFile p f = do
    Right str <- readFile f | (Left err) => pure (Left (show err))
    case parse f p str of
      Left err  => pure (Left err)
      Right res => pure (Right $ processDoc res)

readEddaSentance : Parser (EddaRaw INLINE)
                -> String
                -> Either String (Edda SNIPPET)
readEddaSentance p s =
  case parse (some p) s of
    Left err  => Left err
    Right res => Right $ (processSnippet $ Snippet res IsInLine)

readEddaBody : Parser (EddaRaw BLOCK)
        -> String
        -> Either String (Edda SNIPPET)
readEddaBody p ps =
  case parse (some p) ps of
    Left err  => Left err
    Right res => Right $ processSnippet $ Snippet res IsBlock

-- --------------------------------------------------------------------- [ EOF ]
