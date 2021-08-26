-- ----------------------------------------------------------------- [ Org.idr ]
-- Module    : Org.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
module Text.Markup.Edda.Reader.Org

import Effects
import Effect.File

import public Lightyear
import public Lightyear.Char
import public Lightyear.Strings

import Data.AVL.Dict

import Lightyear
import Lightyear.Char
import Lightyear.Strings

import Text.Markup.Edda.Model.Common
import Text.Markup.Edda.Model.Raw
import Text.Markup.Edda.Model.Processed

import Text.Markup.Edda.Process.Utils
import Text.Markup.Edda.Reader.Common
import Text.Markup.Edda.Reader.Utils

%default partial
%access private

-- --------------------------------------------------------------------- [ Org ]

code : Parser (EddaRaw INLINE)
code = map (Raw CodeTy) (quoted '~') <?> "Code"

verb : Parser (EddaRaw INLINE)
verb = map (Raw VerbTy) (quoted '=') <?> "Verb"

math : Parser (EddaRaw INLINE)
math = map (Raw MathTy) (quoted '$') <?> "Math"

markup : MarkupTy -> Char -> Parser (EddaRaw INLINE)
markup mTy c = do
    txt <- between (char c) (char c) (some mText)
    pure $ Mark mTy txt
  <?> "Markup"

bold : Parser (EddaRaw INLINE)
bold = markup BoldTy '*' <?> "Bold"

emph : Parser (EddaRaw INLINE)
emph = markup EmphTy '/'  <?> "Emph"

strike : Parser (EddaRaw INLINE)
strike = markup StrikeTy '+' <?> "Strike"

uline : Parser (EddaRaw INLINE)
uline = markup UlineTy '_' <?> "Uline"

expLink : Parser (EddaRaw INLINE)
expLink = do
    txt <- brackets $ brackets url
    pure $ Link ExposedTy txt Nil
  <?> "Exposed Link"

hyper : Parser (EddaRaw INLINE)
hyper = do
    (uri, desc) <- brackets internal
    pure $ Link HyperTy uri desc
  where
    internal : Parser (String, List (EddaRaw INLINE))
    internal = do
      u <- brackets url
      d <- brackets $ some (text <* spaces)
      pure (u, intersperse (Punc ' ' ) d)

link : Parser (EddaRaw INLINE)
link = hyper <|> expLink <?> "Link"

fnote : Parser (EddaRaw INLINE)
fnote = do
   (l,d) <- brackets doFnote
   pure $ Link FnoteTy (fromMaybe "" l) d
 where
   doFnote : Parser (Maybe String, (List (EddaRaw INLINE)))
   doFnote = do
     string "fn"
     colon
     lab <- opt word
     colon
     desc <- opt $ some text
     pure (lab, fromMaybe Nil desc)

export
inline : Parser (EddaRaw INLINE)
inline = text
     <|> fnote <|> link
     <|> bold <|> emph <|> strike <|> uline
     <|> code <|> verb <|> math <|> punc
     <?> "Raw Inline"

-- -------------------------------------------------------------- [ Properties ]

export
attribute : String -> Parser (String, String)
attribute key = do
    string "#+" *> string key
    colon
    ps <- manyTill anyChar endOfLine
    pure (key, pack ps)
  <?> "Raw Attribute"

property : Parser (String, String)
property = attribute "PROPERTY" <?> "Property"

inlineKeyWord : String -> Parser (String, List (EddaRaw INLINE))
inlineKeyWord key = do
    string "#+" *> string key
    colon
    spaces
    ps <- manyTill inline endOfLine
    pure (key, ps)
  <?> "Attribute."

caption : Parser (List (EddaRaw INLINE))
caption = do
    (k,v) <- inlineKeyWord "CAPTION"
    pure v
  <?> "Caption"

label : Parser String
label = do
    (k,v) <- attribute "NAME"
    pure v
  <?> "Label"

target : Parser String
target = angles $ angles url
  <?> "Target"

title : Parser (List (EddaRaw INLINE))
title = do
    (k,v) <- inlineKeyWord "TITLE"
    pure v
  <?> "Label"

-- ----------------------------------------------------------------- [ Drawers ]

propEntry : Parser (String, String)
propEntry = do
    colon
    key <- word
    colon
    spaces
    value <- manyTill anyChar endOfLine
    pure (key, pack value)
  <?> "Property Entry"

drawer : Parser $ List (String, String)
drawer = do
    string ":PROPERTIES:"
    endOfLine
    ps <- some propEntry
    token ":END:"
    pure ps
  <?> "Property Drawer"
-- ------------------------------------------------------------------ [ Blocks ]

getOrgBlockType : String -> Either VerbBlockTy TextBlockTy
getOrgBlockType str = case str of
    "COMMENT"     => Left CommentTy
    "SRC"         => Left ListingTy
    "EXAMPLE"     => Left LiteralTy
    "EQUATION"    => Left EquationTy
    "QUOTE"       => Right QuotationTy
    "VERSE"       => Right QuotationTy
    "THEOREM"     => Right TheoremTy
    "COROLLARY"   => Right CorollaryTy
    "LEMMA"       => Right LemmaTy
    "PROPOSITION" => Right PropositionTy
    "PROOF"       => Right ProofTy
    "DEFINITION"  => Right DefinitionTy
    "EXERCISE"    => Right ExerciseTy
    "NOTE"        => Right NoteTy
    "PROBLEM"     => Right ProblemTy
    "QUESTION"    => Right QuestionTy
    "REMARK"      => Right RemarkTy
    "SOLUTION"    => Right SolutionTy
    otherwise     => Left LiteralTy

export
block : Parser (EddaRaw BLOCK)
block = do
    cap  <- opt caption
    lab  <- opt label
    attr <- opt $ attribute "ATTR"
    string "#+BEGIN_"
    ty <- word
    case getOrgBlockType ty of
      Left x => do
        srcopts <- opt $ space  *> manyTill anyChar endOfLine
        let as = dealWithSrcAttrs (convertOpts srcopts) (convertAttrs attr)

        txt <- manyTill anyChar (string "#+END_" *> token ty)
        pure $ VerbBlock x lab (fromMaybe Nil cap) as (pack txt)
      Right y => do
        txt <- manyTill inline (string "#+END_" *> token ty)
        pure $ TextBlock y lab (fromMaybe Nil cap) (convertAttrs attr) txt

   <?> "Blocks"

figure : Parser (EddaRaw BLOCK)
figure = do
    cap <- caption
    lab <- label
    as  <- opt $ some (attribute "ATTR")
    img <- expLink
    spaces
    let attrs = maybe empty (fromList) as
    pure (Figure (Just lab) cap attrs img)
  <?> "Figure"

export
para : Parser (EddaRaw BLOCK)
para = do
    txt <- manyTill inline (endOfLine *> endOfLine)
    spaces
    pure $ TextBlock ParaTy Nothing Nil empty txt
  <?> "Paragraphs"

paraLast : Parser (EddaRaw BLOCK)
paraLast = do
    txt <- manyTill inline (endOfLine *> spaces)
    pure $ TextBlock ParaTy Nothing Nil empty txt
  <?> "Filthy hack for last para"

hrule : Parser (EddaRaw BLOCK)
hrule = do
    token "-----"
    pure HRule

ulMarker : Parser ()
ulMarker = char' '+' <|> char' '-' <?> "UList Marker"

olMarker : Parser ()
olMarker = marker '.' <|> marker ')'
  where
    marker : Char -> Parser ()
    marker c = do
      some $ digit
      char c
      spaces
      pure ()

-- @TODO Add coninuations
listItem : Parser () -> Parser (List (EddaRaw INLINE))
listItem mark = do
    mark
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
  <?> "Bulleted lists"

dlist : Parser (EddaRaw BLOCK)
dlist = do
    is <- some defItem <* endOfLine
    pure $ DList is
  <?> "Description Lists"
  where
    marker : Parser (List (EddaRaw INLINE))
    marker = ulMarker *> space *> manyTill inline (spaces *> colon *> colon)
        <?> "Desc Marker"

    defItem : Parser (List (EddaRaw INLINE), List (EddaRaw INLINE))
    defItem = do
        key <- marker
        spaces
        values <- manyTill inline endOfLine
        pure (key, values)
      <?> "Desc Lists"

list : Parser (EddaRaw BLOCK)
list = dlist <|> blist <|> olist <?> "Lists"

export
header : Parser (EddaRaw BLOCK)
header = char '*' >! do
    depth <- opt (many $ char '*')
    let d = length (fromMaybe [] depth) + 1
    spaces
    title <- manyTill (inline) (endOfLine)
    l <- opt target
    spaces
    as <- opt drawer
    let attrs = maybe empty (fromList) as
    pure $ Heading d l title attrs

export
orgBlock : Parser (EddaRaw BLOCK)
orgBlock = header <|> block <|> list <|> figure <|> hrule <|> para <?> "Org Blocks"

parseOrg : Parser (EddaRaw DOC)
parseOrg = do
  title'  <- title
  author <- attribute "AUTHOR"
  date   <- attribute "DATE" <* space
  txt    <- many orgBlock
  lpara  <- many paraLast -- Dirty Hack
  let ps = fromList [author, date]
  let txt' = intersperse Empty txt
  pure $ Doc title' ps (txt' ++ [Empty] ++ lpara)
 <?> "Raw Org Mode"

-- -------------------------------------------------------------------- [ Read ]

namespace Doc
  export
  fromOrgE : String -> Eff (Either String (Edda DOC)) [FILE ()]
  fromOrgE = assert_total $ readEddaFileE parseOrg

  export
  fromOrg : String -> IO (Either String (Edda DOC))
  fromOrg = assert_total $ readEddaFile parseOrg

namespace Snippet
  namespace Inline
    export
    fromOrg : String -> Either String (Edda SNIPPET)
    fromOrg = assert_total $ readEddaSentance inline

  namespace Para
    export
    fromOrg : String -> Either String (Edda SNIPPET)
    fromOrg s = assert_total $ readEddaBody orgBlock (s ++ "\n\n")

-- --------------------------------------------------------------------- [ EOF ]
