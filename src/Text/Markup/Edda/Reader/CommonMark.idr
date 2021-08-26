-- ---------------------------------------------------------- [ CommonMark.idr ]
-- Module    : CommonMark.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

module Text.Markup.Edda.Reader.CommonMark

import Data.AVL.Dict

import Effects
import Effect.File

import public Lightyear
import public Lightyear.Char
import public Lightyear.Strings

import Text.Markup.Edda.Model

import Text.Markup.Edda.Reader.Utils
import Text.Markup.Edda.Reader.Common

%access private
%default partial

-- ------------------------------------------------------------------ [ Inline ]

code : Parser (EddaRaw INLINE)
code = map (Raw CodeTy) (quoted '`') <?> "Code"

markup : MarkupTy -> String -> Parser (EddaRaw INLINE)
markup mTy c = do
    txt <- between (string c) (string c) (some mText)
    pure $ Mark mTy txt
  <?> "Markup"

bold : Parser (EddaRaw INLINE)
bold = markup BoldTy "**" <|> markup BoldTy "__" <?> "Bold"

emph : Parser (EddaRaw INLINE)
emph = markup EmphTy "*" <|> markup EmphTy "_" <?> "Emph"

expLink : Parser (EddaRaw INLINE)
expLink = do
  txt <- angles url
  pure $ Link ExposedTy txt Nil

hyper : Parser (EddaRaw INLINE)
hyper = do
  d <- brackets $ some (text <* spaces)
  uri  <- parens $ url
  let desc = intersperse (Punc ' ') d
  pure $ Link HyperTy uri (desc)

link : Parser (EddaRaw INLINE)
link = hyper <|> expLink <?> "Links"

inline : Parser (EddaRaw INLINE)
inline = text
     <|> link
     <|> bold
     <|> emph
     <|> code
     <|> punc
     <?> "Raw Inline"

figure : Parser (EddaRaw BLOCK)
figure = do
    char '!'
    d <- brackets $ some text
    let desc = intersperse (Punc ' ') d
    uri <- parens url
    let img = Link ExposedTy uri Nil
    endOfLine
    endOfLine
    pure (Figure (Just "") desc empty img)
  <?> "Figure"

-- ------------------------------------------------------------------- [ Lists ]
ulMarker : Parser ()
ulMarker = char' '+' <|> char' '-' <|> char' '*' <?> "UList Marker"

olMarker : Parser ()
olMarker = marker '.' <|> marker ')'
  where
    marker : Char -> Parser ()
    marker c = do
      some $ digit
      char c
      (satisfy isSpace)
      pure ()

-- @TODO Add coninuations
listItem : Parser () -> Parser (List (EddaRaw INLINE))
listItem mark = do
    mark
    space
    line <- manyTill inline endOfLine
    pure $ line

olist : Parser (EddaRaw BLOCK)
olist = do
    is <- some (listItem olMarker)
    endOfLine
    pure $ ListBlock NumberTy is

blist : Parser (EddaRaw BLOCK)
blist = do
    is <- some (listItem ulMarker)
    endOfLine
    pure $ ListBlock BulletTy is

list : Parser (EddaRaw BLOCK)
list = blist <|> olist

-- ------------------------------------------------------------------ [ Blocks ]

indentedcode : Parser (EddaRaw BLOCK)
indentedcode = identcode "\t" <|> identcode "    " <?> "Indented Code Block"
  where
    identcode : String -> Parser (EddaRaw BLOCK)
    identcode m = do
      ss <- some $ (string m *!> manyTill (anyChar) endOfLine)
      endOfLine
      let src = concatMap (\x => pack (List.(++) x ['\n'])) ss
      pure $ VerbBlock LiteralTy Nothing Nil empty src
     <?> "Indented Code"

fencedcode : Parser (EddaRaw BLOCK)
fencedcode = fencedcode' "```" <|> fencedcode' "~~~" <?> "Fenced Code Block"
  where
    fencedcode' : String -> Parser (EddaRaw BLOCK)
    fencedcode' m = do
        string m
        srcopts <- opt $ space *> manyTill (anyChar) endOfLine
        let as = dealWithSrcAttrs (convertOpts srcopts) empty
        src <- manyTill anyChar (string m)
        endOfLine
        pure $ VerbBlock ListingTy Nothing Nil as (pack src)
      <?> "Fenced Code Block: " ++ m

blockquote : Parser (EddaRaw BLOCK)
blockquote = do
    txt <- some $ (token ">" *!> manyTill inline endOfLine)
    endOfLine
    let p = concat txt
    pure $ TextBlock QuotationTy Nothing Nil empty p

-- ------------------------------------------------------------------- [ Paras ]
para : Parser (EddaRaw BLOCK)
para = do
    txt <- manyTill (inline) (endOfLine *> endOfLine)
    pure $ TextBlock ParaTy Nothing Nil empty txt
  <?> "Paragraphs"

paraLast : Parser (EddaRaw BLOCK)
paraLast = do
    txt <- manyTill inline (endOfLine *> spaces)
    pure $ TextBlock ParaTy Nothing Nil empty txt
  <?> "Filthy hack for last para"

hrule : Parser (EddaRaw BLOCK)
hrule = hrule' "***" <|> hrule' "---" <|> hrule' "___" <?> "hrules"
  where
    hrule' m = do
      string m
      endOfLine
      pure $ HRule

empty : Parser (EddaRaw BLOCK)
empty = do
  endOfLine
  endOfLine
  pure $ Empty

header : Parser (EddaRaw BLOCK)
header = char '#' >! do
    depth <- opt (many $ char '#')
    spaces
    title <- manyTill (inline) (endOfLine)
    endOfLine
    let d = length (fromMaybe Nil depth) + 1
    pure (Heading d Nothing title empty)
  <?> "Header"

block : Parser (EddaRaw BLOCK)
block = header
    <|> blockquote <|> indentedcode <|> fencedcode
    <|> list <|> figure <|> hrule <|> para <|> empty
    <?> "Block"

parseCommonMark : Parser (EddaRaw DOC)
parseCommonMark = do
    txt <- some block
    let txt' = intersperse (Empty) txt
    pure $ Doc Nil empty (txt' ++ [Empty])
  <?> "Raw Common Mark"

-- -------------------------------------------------------------------- [ Read ]

namespace Doc
  export
  fromCommonMarkE : String -> Eff (Either String (Edda DOC)) [FILE ()]
  fromCommonMarkE = assert_total $ readEddaFileE parseCommonMark

  export
  fromCommonMark : String -> IO (Either String (Edda DOC))
  fromCommonMark = assert_total $ readEddaFile parseCommonMark

namespace Snippet
  namespace Inline
    export
    fromCommonMark : String -> Either String (Edda SNIPPET)
    fromCommonMark = assert_total $ readEddaSentance inline

  namespace Para
    export
    fromCommonMark : String -> Either String (Edda SNIPPET)
    fromCommonMark s = assert_total $ readEddaBody block (s ++ "\n\n")

-- --------------------------------------------------------------------- [ EOF ]
