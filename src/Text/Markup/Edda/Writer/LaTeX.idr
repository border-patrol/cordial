-- --------------------------------------------------------------- [ LaTeX.idr ]
-- Module    : LaTeX.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
module Text.Markup.Edda.Writer.LaTeX

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

macro : String -> String -> String
macro c s = concat ["\\", c, "{", s, "}"]

-- ----------------------------------------------------------- [ Write Inlines ]

mutual
  export
  inlines : List (Edda INLINE) -> String
  inlines xs = assert_total (concatMap inline xs)

  parens : String -> String -> List (Edda INLINE) -> String
  parens l r ts = concat [l, inlines ts, r]

  link : String -> List (Edda INLINE) -> String
  link uri Nil  = macro "url"  uri
  link uri desc = concat [macro "href" uri, "{", inlines desc, "}"]

  inline : Edda INLINE -> String
  inline (Text t) = t
  inline (Sans t) = macro "textsf" t
  inline (Scap t) = macro "textsc" t
  inline (Mono t) = macro "texttt" t
  inline (Verb v)     = "\\verb!" ++ v ++ "!"
  inline (Code v)     = macro "texttt" v
  inline (Math v)     = "$" ++ v ++ "$"
  inline (Emph t)     = macro "emph"      (inlines t)
  inline (Bold t)     = macro "textbf"    (inlines t )
  inline (Strike t)   = macro "sout"      (inlines t)
  inline (Uline t)    = macro "underline" (inlines t)
  inline (Quote ty t) =
    case ty of
      SQuote => macro "squote" (inlines t)
      DQuote => macro "dquote" (inlines t)
  inline (Parens ty t) =
    case ty of
      Parents  => parens "("   ")"   t
      Brackets => parens "["   "]"   t
      Braces   => parens "\\{" "\\}" t
  inline (Ref url)        = link url Nil
  inline (Hyper uri desc) = link uri desc
  inline (FNote l d)   = macro "footnote" (inlines d)
  inline (Cite ty uri) =
    case ty of
      ParenSty => (macro "cite"  uri)
      TextSty  => (macro "citet" uri)
  inline (MiscPunc c) =
    case c of
      '%' => "\\%"
      '_' => "\\_"
      '^' => "\\^"
      '~' => "\\~"
      c   => cast c
  inline Space      = " "
  inline Newline    = "\n"
  inline Tab        = "\t"
  inline LBrace     = "\\{"
  inline RBrace     = "\\}"
  inline LParen     = "("
  inline RParen     = ")"
  inline LBrack     = "["
  inline RBrack     = "]"
  inline LAngle     = "\\textless"
  inline RAngle     = "\\textgreater"
  inline Dollar     = "\\$"
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
  inline Ellipsis   = "\\ldots"
  inline Hyphen     = "-"
  inline Bang       = "!"
  inline Period     = "."
  inline QMark      = "?"
  inline Hash       = "\\#"
  inline Equals     = "="
  inline Pipe       = "$\\mid$"

-- ----------------------------------------------------- [ Write Generic Block ]
env : String -> String -> String
env n body = unlines
    [ macro "begin" (toLower n)
    , body
    , macro "end" (toLower n)]


thm : String
   -> Maybe String
   -> List (Edda INLINE)
   -> List (Edda INLINE)
   -> String
thm e l c b = env (toLower e) body
  where
    body : String
    body = unlines
      [ "[" ++ inlines c ++ "]"
      , strFromMaybe (macro "label") l
      , inlines b
      ]

figure : Maybe String
      -> List (Edda INLINE)
      -> String
      -> String
figure l c body = env ("figure") body'
  where
    body' : String
    body' = unlines
      [ body
      , macro "caption" $ inlines c
      , macro "label"   $ fromMaybe "missing" l
      ]


-- Make generic
list : String -> List (List (Edda INLINE)) -> String
list s is = env s (unlines $ map item is)
  where
    item : List (Edda INLINE) -> String
    item bs = unwords ["\\item", inlines bs, "\n"]

dlist : List (Pair (List (Edda INLINE)) (List (Edda INLINE))) -> String
dlist kvs = env "description" (unlines $ map descItem kvs)
  where
    descItem : (List (Edda INLINE), List (Edda INLINE)) -> String
    descItem (k,v) = unwords ["\\item[" ++ inlines k ++ "]", inlines v]

secLvl : Nat -> List (Edda INLINE) -> String
secLvl Z                 t = macro "section"       (inlines t)
secLvl (S Z)             t = macro "subsection"    (inlines t)
secLvl (S (S Z))         t = macro "subsubsection" (inlines t)
secLvl (S (S (S Z)))     t = macro "paragraph"     (inlines t)
secLvl (S (S (S (S Z)))) t = macro "subparagraph"  (inlines t)
secLvl _                 t = inlines t ++ " % Depth not recognised\n"

-- ------------------------------------------------------------- [ Write Block ]
-- deal with attrs
||| Write block to LaTeX version.
export
block : Edda BLOCK -> String
block (HRule) = "\\hrulefill"
block (Empty) = "\n"
block (Section lvl label title as body) = assert_total $
    unlines $ unwords [ secLvl lvl title
                      , strFromMaybe (macro "label") label
                      , "\n"]
              :: map block body

block (Figure l c as fig) = figure l c (inline fig)
block (DList kvs)         = dlist kvs
block (OList bs)          = list "itemize"  bs
block (BList bs)          = list "enumerate" bs

block (Para txt) = inlines txt ++ "\n\n"

block (Listing l c lang langopts as src) = figure l c (env "verbatim" src)

block (Comment ss)          = env "comment" ss
block (Equation l eq)       = env "equation" eq  -- Add support for caption and label
block (Literal l c src)     = env "verbatim" src -- Add support for caption and label

block (Quotation l txt)     = thm "QUOTE" l Nil txt
block (Theorem l c txt)     = thm "Theorem" l c txt
block (Corollary l c txt)   = thm "COROLLARY" l c txt
block (Lemma l c txt)       = thm "LEMMA" l c txt
block (Proposition l c txt) = thm "PROPOSITION" l c txt
block (Proof l c txt)       = thm "PROOF" l c txt
block (Definition l c txt)  = thm "DEFINITION" l c txt
block (Exercise l c txt)    = thm "EXERCISE" l c txt
block (Note l c txt)        = thm "NOTE" l c txt
block (Remark l c txt)      = thm "REMARK" l c txt
block (Problem l c txt)     = thm "PROBLEM" l c txt
block (Question l c txt)    = thm "QUESTION" l c txt
block (Solution l c txt)    = thm "SOLUTION" l c txt
block (Example l c txt)     = thm "EXAMPLE" l c txt

export
blocks : (List (Edda BLOCK)) -> String
blocks = concatMap block
-- -------------------------------------------------------- [ Write List (String, String) ]

properties : List (Edda INLINE) -> Dict String String -> String
properties t ps  = unlines
    [ macro "title"  $ inlines t
    , macro "author" $ fromMaybe "author missing" (lookup "AUTHOR" ps)
    , macro "date"   $ fromMaybe "date missing"   (lookup "DATE" ps)
    , "\n"
    ]

-- --------------------------------------------------------------- [ Write Org ]

namespace Doc
  --@ TODO Add customisable preamble, and standalone
  ||| Convert document to LaTeX instance.
  export
  toLaTeX : Edda DOC -> String
  toLaTeX (Doc title ps body) = unlines
      [ """\documentclass{article}
  \usepackage{thmtools}
  \usepackage[normelem]{ulem}
  \usepackage{hyperref}

  \declaretheoremstyle[%
    spaceabove=6pt, spacebelow=6pt,
    headfont=\normalfont\bfseries,
    bodyfont=\normalfont\em,
    postheadspace=1em
  ]{thmstyle}

  \declaretheoremstyle[%
    spaceabove=6pt, spacebelow=6pt,
    headfont=\normalfont\bfseries,
    bodyfont=\normalfont,
    postheadspace=1em
  ]{notestyle}

  \newcommand{\squote}[1]{`#1'}
  \newcommand{\dquote}[1]{``#1''}

  \declaretheorem[style=notestyle, starred, name={\textbf{Note}}]{note}
  \declaretheorem[style=notestyle, starred, name={\textbf{Remark}}]{remark}
  \declaretheorem[style=thmstyle, name={Definition}]{definition}
  \declaretheorem[style=thmstyle, name={Example}]{example}
  \declaretheorem[style=thmstyle, name={Exercise}]{exercise}
  \declaretheorem[style=thmstyle, name={Problem}]{problem}
  \declaretheorem[style=thmstyle, name={Question}]{question}
  \declaretheorem[style=thmstyle, name={Solution}]{solution}

  \declaretheorem[style=thmstyle, name={Corollary}]{corollary}
  \declaretheorem[style=thmstyle, name={Lemma}]{lemma}
  \declaretheorem[style=thmstyle, name={Proposition}]{proposition}
  \declaretheorem[style=thmstyle, name={Theorem}]{theorem}
  """
      , properties title ps
      , "\\begin{document}\n\\maketitle"
      , concatMap block body
      , "\\end{document}"
      ]

namespace File

  ||| Write LaTeX representation to file.
  export
  toLaTeXE : String
            -> Edda DOC
            -> Eff (FileOpSuccess) [FILE ()]
  toLaTeXE fn doc = writeEddaFileE toLaTeX fn doc

  ||| Write LaTeX representation to file.
  export
  toLaTeX : String
           -> Edda DOC
           -> IO (Either FileError ())
  toLaTeX fn doc = writeEddaFile toLaTeX fn doc


namespace Snippet
  ||| Convert edda document to latex.
  export
  toLaTeX : Edda SNIPPET -> String
  toLaTeX (Snippet snippet prf) with (prf)
    toLaTeX (Snippet snippet prf) | IsInLine = inlines snippet
    toLaTeX (Snippet snippet prf) | IsBlock = blocks snippet

-- --------------------------------------------------------------------- [ EOF ]
