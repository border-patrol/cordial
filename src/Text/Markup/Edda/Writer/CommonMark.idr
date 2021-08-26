-- ----------------------------------------------------------------- [ Org.idr ]
-- Module    : Org.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
module Text.Markup.Edda.Writer.CommonMark

import Data.AVL.Dict

import Effects
import Effect.File
import Effect.Exception

import Text.Markup.Edda.Model
import Text.Markup.Edda.Process.Utils

import Text.Markup.Edda.Writer.Common

-- -------------------------------------------------------------- [ Directives ]
%default total
%access private

-- @TODO Attributes...

-- ------------------------------------------------------------ [ Misc Writing ]
ntimes : Char -> Nat -> String
ntimes c n = concat $ ntimes' (S n)
  where
    ntimes' : Nat -> List String
    ntimes' Z     = Nil
    ntimes' (S k) = (cast c) :: ntimes' k

-- ----------------------------------------------------------- [ Write Inlines ]

mutual
  export
  inlines : List (Edda INLINE) -> String
  inlines xs = assert_total $ concatMap inline xs

  parens : String -> String -> Either String (List (Edda INLINE)) -> String
  parens l r (Left str) = concat [l, str,        r]
  parens l r (Right ts) = concat [l, inlines ts, r]

  markup : String -> Either String (List (Edda INLINE)) -> String
  markup t txt = parens t t txt

  link : String -> List (Edda INLINE) -> String
  link uri Nil  = concat ["<", uri, ">"]
  link uri desc = concat ["[", uri, "](", inlines desc, ")"]

  inline : Edda INLINE -> String
  inline (Text t)     = t
  inline (Sans t)     = t
  inline (Scap t)     = t
  inline (Mono t)     = t
  inline (Verb v)     = markup "`"  (Left v)
  inline (Code v)     = markup "`"  (Left v)
  inline (Math v)     = markup "`"  (Left v)
  inline (Emph t)     = markup "*"  (Right t)
  inline (Bold t)     = markup "**" (Right t)
  inline (Strike t)   = markup "~~" (Right t)
  inline (Uline t)    = markup "*"  (Right t)
  inline (Quote ty t) =
    case ty of
      SQuote => markup "'"  (Right t)
      DQuote => markup "\"" (Right t)
  inline (Parens ty t) =
    case ty of
      Parents  => parens "(" ")" (Right t)
      Brackets => parens "[" "]" (Right t)
      Braces   => parens "{" "}" (Right t)
  inline (Ref url)        = link url Nil
  inline (Hyper uri desc) = link uri desc
  inline (FNote l d) =
    case d of
      Nil => parens "`" "`" (Left (concat ["fn", ":", l, ":"]))
      x   => parens "`" "`" (Right ([Text ("fn:" ++ l ++ ":")] ++ x))
  inline (Cite ty uri) =
    case ty of
      ParenSty => ("`citep:" ++ uri ++ "`")
      TextSty  => ("`citet:" ++ uri ++ "`")
  inline (MiscPunc c) = (cast c)
  inline Space      = " "
  inline Newline    = "\n"
  inline Tab        = "\t"
  inline LBrace     = "{"
  inline RBrace     = "}"
  inline LParen     = "("
  inline RParen     = ")"
  inline LBrack     = "["
  inline RBrack     = "]"
  inline LAngle     = "<"
  inline RAngle     = ">"
  inline Dollar     = "$"
  inline Colon      = ":"
  inline Semi       = ";"
  inline EnDash     = "--"
  inline EmDash     = "---"
  inline FSlash     = "/"
  inline BSlash     = "\\"
  inline Apostrophe = "'"
  inline SMark      = "\""
  inline Comma      = ","
  inline Plus       = "+"
  inline Ellipsis   = "..."
  inline Hyphen     = "-"
  inline Bang       = "!"
  inline Period     = "."
  inline QMark      = "?"
  inline Hash       = "#"
  inline Equals     = "="
  inline Pipe       = "|"

-- ----------------------------------------------------- [ Write Generic Block ]

genblock : (a -> String)
        -> a
        -> String
genblock f b = unlines [ f b, "\n"]

textblock : List (Edda INLINE)
         -> String
textblock = genblock (inlines)

verbblock : String
         -> String
verbblock = genblock (\x => ">" ++ x)

-- ------------------------------------------------------------- [ Write Block ]

itemDef : (List (Edda INLINE), List (Edda INLINE)) -> String
itemDef (k,vs) =
    unwords ["+", markup "*" (Left $ inlines k), "::", inlines vs]

item : String -> List (Edda INLINE) -> String
item m b = unwords [m, inlines b]

export
block : Edda BLOCK -> String
block (HRule) = "-----"
block (Empty) = "\n"
block (Section lvl label title as body) =
   assert_total (unlines $ unwords [ntimes '#' lvl, inlines title, fromMaybe "" label] :: (map block body))
block (Figure l c as fig) = unlines [inline fig, "\n"]

block (DList kvs) = (unlines $ map itemDef kvs)
block (OList bs)        = (unlines $ map (item "1.") bs)
block (BList bs)        = (unlines $ map (item "*")  bs)
block (Para txt)        = inlines txt

block (Listing l c lang langopts as src) =
    unlines [ "\n```" ++ fromMaybe "" lang , src, "```"]

block (Comment ss)          = verbblock ss
block (Equation l eq)       = verbblock eq
block (Literal l c src)     = verbblock src

block (Quotation l txt)     = textblock txt

block (Theorem l c txt)     = textblock txt
block (Corollary l c txt)   = textblock txt
block (Lemma l c txt)       = textblock txt
block (Proposition l c txt) = textblock txt
block (Proof l c txt)       = textblock txt
block (Definition l c txt)  = textblock txt
block (Exercise l c txt)    = textblock txt
block (Note l c txt)        = textblock txt
block (Remark l c txt)      = textblock txt
block (Problem l c txt)     = textblock txt
block (Question l c txt)    = textblock txt
block (Solution l c txt)    = textblock txt
block (Example l c txt)     = textblock txt

blocks : List (Edda BLOCK) -> String
blocks = concatMap block

-- -------------------------------------------------------- [ Write List (String, String) ]

properties : List (Edda INLINE) -> Dict String String -> String
properties t ps =
  unlines [ "%YAML 1.2\n---"
          , concat ["title:",  inlines t]
          , concat ["author:", fromMaybe "author missing" (lookup "AUTHOR" ps)]
          , concat ["date:",   fromMaybe "date missing"   (lookup "DATE" ps)]
          , "...\n"
          ]

-- -------------------------------------------------------- [ Write CommonMark ]

namespace Doc
  ||| Convert edda document to markdown.
  export
  toCommonMark : Edda DOC -> String
  toCommonMark (Doc title attrs body) =
     let attrsStr = properties title attrs in
       unlines $ attrsStr :: map block body

namespace File
  ||| Write document to a markdown file.
  export
  toCommonMarkE : String
                 -> Edda DOC
                 -> Eff (FileOpSuccess) [FILE ()]
  toCommonMarkE fn doc = writeEddaFileE toCommonMark fn doc

  ||| Write document to a markdown file.
  export
  toCommonMark : String
                 -> Edda DOC
                 -> IO (Either FileError ())
  toCommonMark fn doc = writeEddaFile toCommonMark fn doc

namespace Snippet
  ||| Convert edda document to markdown.
  export
  toCommonMark : Edda SNIPPET -> String
  toCommonMark (Snippet snippet prf) with (prf)
    toCommonMark (Snippet snippet prf) | IsInLine = inlines snippet
    toCommonMark (Snippet snippet prf) | IsBlock = blocks snippet



-- --------------------------------------------------------------------- [ EOF ]
