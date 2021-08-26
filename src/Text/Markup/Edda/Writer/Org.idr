-- ----------------------------------------------------------------- [ Org.idr ]
-- Module    : Org.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
module Text.Markup.Edda.Writer.Org

import Data.AVL.Dict

import Effects
import Effect.File
import Effect.Exception

import Text.Markup.Edda.Model

import Text.Markup.Edda.Writer.Common

-- -------------------------------------------------------------- [ Directives ]
%default total
%access private

-- ------------------------------------------------------------ [ Misc Writing ]
rawtag : String -> String -> String
rawtag k v = unwords ["#+" ++ k ++ ":", v]

ntimes : Char -> Nat -> String
ntimes c n = concat $ ntimes' (S n)
  where
    ntimes' : Nat -> List String
    ntimes' Z     = Nil
    ntimes' (S k) = (cast c) :: ntimes' k

attrs : Dict String String -> String
attrs as = rawtag "ATTR" (unwords as')
  where
    as' : List String
    as' = map (\(k,v) => k ++ ":" ++ v) (Dict.toList as)

-- ----------------------------------------------------------- [ Write Inlines ]

mutual

  |||  Convert the list of inlines to their org mode representation.
  export
  inlines : List (Edda INLINE) -> String
  inlines xs = assert_total $ concatMap inline xs

  parens : Char -> Char -> Either String (List (Edda INLINE)) -> String
  parens l r (Left str) = concat [cast l, str,        cast r]
  parens l r (Right ts) = concat [cast l, inlines ts, cast r]

  markup : Char -> Either String (List (Edda INLINE)) -> String
  markup t txt = parens t t txt

  link : String -> List (Edda INLINE) -> String
  link uri Nil  = concat ["[[", uri, "]]"]
  link uri desc = concat ["[[", uri, "][", inlines desc, "]]"]

  inline : Edda INLINE -> String
  inline (Text t) = t
  inline (Sans t) = t
  inline (Scap t) = t
  inline (Mono t) = t
  inline (Verb v)     = markup '=' (Left v)
  inline (Code v)     = markup '~' (Left v)
  inline (Math v)     = markup '$' (Left v)
  inline (Emph t)     = markup '/' (Right t)
  inline (Bold t)     = markup '*' (Right t)
  inline (Strike t)   = markup '+' (Right t)
  inline (Uline t)    = markup '_' (Right t)
  inline (Quote ty t) =
    case ty of
      SQuote => markup '\'' (Right t)
      DQuote => markup '\"' (Right t)
  inline (Parens ty t) =
    case ty of
      Parents  => parens '(' ')' (Right t)
      Brackets => parens '[' ']' (Right t)
      Braces   => parens '{' '}' (Right t)
  inline (Ref url)        = link url Nil
  inline (Hyper uri desc) = link uri desc
  inline (FNote l d) =
    case d of
      Nil => parens '[' ']' (Left (concat ["fn", ":", l, ":"]))
      x   => parens '[' ']' (Right ([Text ("fn:" ++ l ++ ":")] ++ x))
  inline (Cite ty uri) =
    case ty of
      ParenSty => ("[[citep:" ++ uri ++ "]]")
      TextSty  => ("[[citet:" ++ uri ++ "]]")
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

tag : String -> List (Edda INLINE) -> String
tag k vs = unlines [rawtag k (inlines vs)]

-- ----------------------------------------------------- [ Write Generic Block ]

genblock : (a -> String)
        -> String
        -> Maybe String
        -> List (Edda INLINE)
        -> a
        -> String
genblock f t l c b = unlines
  [ tag "CAPTION" c
  , strFromMaybe (\x => rawtag "NAME" x) l
  , "#+BEGIN_" ++ t
  , f b
  , "#+END_" ++ t
  ]

textblock : String
         -> Maybe String
         -> List (Edda INLINE)
         -> List (Edda INLINE)
         -> String
textblock = genblock (inlines)

verbblock : String
         -> Maybe String
         -> List (Edda INLINE)
         -> String
         -> String
verbblock = genblock (\x => x)

-- ------------------------------------------------------------- [ Write Block ]

itemDef : (List (Edda INLINE), List (Edda INLINE)) -> String
itemDef (k,vs) = unwords ["-", inlines k, "::", inlines vs]

item : String -> List (Edda INLINE) -> String
item m b = unwords [m, inlines b]


||| Convert a block to their org mode representation
export
block : Edda BLOCK -> String
block (HRule) = "-----"
block (Empty) = ""
block (Section lvl label title as body) = assert_total $
    unlines $ unwords [ ntimes '*' lvl
                      , inlines title
                      , fromMaybe "" label
                      , "\n"]
              :: map block body
block (Figure l c as fig) =
    unlines [ tag "CAPTION" c
            , rawtag "NAME" (fromMaybe "EMPTY" l)
            , attrs as
            , inline fig
            , "\n"]
block (DList kvs) = (unlines $ map itemDef kvs)
block (OList bs)  = (unlines $ map (item "1.") bs)
block (BList bs)  = (unlines $ map (item "+")  bs)
block (Para txt) = inlines txt ++ "\n"
block (Listing l c lang langopts as src) =
    unlines [ tag "CAPTION" c
            , rawtag "NAME" $ fromMaybe "MISSING" l
            , attrs as
            , unwords ["#+BEGIN_SRC", fromMaybe "" lang, fromMaybe "" langopts]
            , src
            , "#+END_SRC"
            ]
block (Comment ss)          = verbblock "COMMENT" Nothing Nil ss
block (Equation l eq)       = verbblock "EQUATION" l Nil eq
block (Literal l c src)     = verbblock "EXAMPLE" l c src
block (Quotation l txt)     = textblock "QUOTE" l Nil txt
block (Theorem l c txt)     = textblock "Theorem" l c txt
block (Corollary l c txt)   = textblock "COROLLARY" l c txt
block (Lemma l c txt)       = textblock "LEMMA" l c txt
block (Proposition l c txt) = textblock "PROPOSITION" l c txt
block (Proof l c txt)       = textblock "PROOF" l c txt
block (Definition l c txt)  = textblock "DEFINITION" l c txt
block (Exercise l c txt)    = textblock "EXERCISE" l c txt
block (Note l c txt)        = textblock "NOTE" l c txt
block (Remark l c txt)      = textblock "REMARK" l c txt
block (Problem l c txt)     = textblock "PROBLEM" l c txt
block (Question l c txt)    = textblock "QUESTION" l c txt
block (Solution l c txt)    = textblock "SOLUTION" l c txt
block (Example l c txt)     = textblock "EXAMPLE" l c txt

||| Convert a list of blocks to their org mode representation.
export
blocks : List (Edda BLOCK) -> String
blocks bs = unlines $ map block bs

-- -------------------------------------------------------- [ Write List (String, String) ]

properties : List (Edda INLINE) -> Dict String String -> String
properties title ps = unlines ts
  where
    ps' : List (String, String)
    ps' = toList ps

    ts : List String
    ts = [ rawtag "TITLE"  $ inlines title ]
         ++
         map (\(k,v) => rawtag k v) ps'
         ++
         ["\n"]

-- --------------------------------------------------------------- [ Write Org ]

namespace Doc
  ||| Return a string containing the org mode representation of the document.
  export
  toOrg : Edda DOC -> String
  toOrg (Doc title ps body) = unlines $ (properties title ps :: map block body)


namespace File
  ||| Write the org mode representation of the given document to file.
  export
  toOrgE : String
          -> Edda DOC
          -> Eff (FileOpSuccess) [FILE ()]
  toOrgE fn doc = writeEddaFileE toOrg fn doc

  export
  toOrg : String
          -> Edda DOC
          -> IO (Either FileError ())
  toOrg fn doc = writeEddaFile toOrg fn doc

namespace Snippet
  export
  toOrg : Edda SNIPPET -> String
  toOrg (Snippet snippet prf) with (prf)
    toOrg (Snippet snippet prf) | IsInLine = inlines snippet
    toOrg (Snippet snippet prf) | IsBlock = blocks snippet

-- --------------------------------------------------------------------- [ EOF ]
