-- --------------------------------------------------------------- [ Utils.idr ]
-- Module    : Utils.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
module Text.Markup.Edda.Reader.Utils

import Data.AVL.Dict

import Lightyear
import Lightyear.Char
import Lightyear.Strings

import Text.Markup.Edda.Model.Common
import Text.Markup.Edda.Model.Raw
import Text.Markup.Edda.Model.Processed

import Text.Markup.Edda.Process.Utils

%access export

-- ------------------------------------------------------------- [ Combinators ]

lexemeL : Monad m => ParserT String m a -> ParserT String m a
lexemeL p = space *> p

lexL : Monad m => ParserT String m a -> ParserT String m a
lexL p = lexemeL p

lex : Monad m => ParserT String m a -> ParserT String m a
lex p = lexeme p

-- ---------------------------------------------------------- [ String Parsers ]

char' : Char -> Parser ()
char' c = char c *> pure ()

private
pathChar : Parser Char
pathChar = urlChar <|> satisfy (isAlphaNum) <?> "Path Char"
  where
    urlChar : Parser Char
    urlChar = do
      c <- satisfy (const True)
      case c of
        '\\' => pure '\\'
        '/'  => pure '/'
        '.'  => pure '.'
        ':'  => pure ':'
        '#'  => pure '#'
        '='  => pure '='
        '?'  => pure '?'
        '-'  => pure '-'
        _    => satisfy (const False)

url : Parser String
url = map pack (some pathChar) <?> "URL"

word : Parser String
word = map pack (some alphaNum) <?> "Word"

punctuation : Parser Char
punctuation = satisfy (\x => not $ isAlphaNum x) <?> "Punctuation"

-- -------------------------------------------------------------- [ Misc Stuff ]

dealWithSrcAttrs : Maybe String
                -> (Dict String String)
                -> (Dict String String)
dealWithSrcAttrs Nothing         as = as
dealWithSrcAttrs (Just srcattrs) as = insert ("src_lang") (trim $ fst foo) $
                                      insert ("src_opts") (trim $ snd foo ) as
  where
    foo : (String, String)
    foo = break (== ' ') srcattrs

convertOpts : Maybe (List Char) -> Maybe String
convertOpts b = case b of
                  Just x => Just (pack x)
                  Nothing => Nothing

convertAttrs : Maybe (String, String) -> Dict String String
convertAttrs Nothing  = empty
convertAttrs (Just (k,v)) = insert k v empty

-- ----------------------------------------------------------------- [ Parsers ]

punc : Parser (EddaRaw INLINE)
punc = map Punc punctuation <?> "Raw Punctuation"

text : Parser (EddaRaw INLINE)
text = map (Font SerifTy) word <?> "Raw Word"

rsvp : List Char
rsvp = ['+', '=', '*', '/', '~', '_']

borderPunc : Parser (Char)
borderPunc = do
    c <- punctuation
    case c of
      ','  => satisfy (const False)
      '\'' => satisfy (const False)
      '\"' => satisfy (const False)
      x    => if x `elem` rsvp
                then satisfy (const False)
                else pure x

mText : Parser (EddaRaw INLINE)
mText = text <|> map Punc borderPunc <?> "Texted used in markup"

-- --------------------------------------------------------------------- [ EOF ]
