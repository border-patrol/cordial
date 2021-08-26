module Text.Markup.Edda.Model.Raw

import Data.AVL.Dict

import Text.Markup.Edda.Model.Common

%default total
%access public export

data EddaRaw : EddaTy -> Type where
-- ------------------------------------------------------------------ [ Inline ]
-- --------------------------------------------------------------------- [ Raw ]
  Font : (ty : FontTy)
      -> (word : String)
      -> EddaRaw INLINE
  Punc : (c : Char)
      -> EddaRaw INLINE

  Link : (ty : LinkTy)
      -> (url  : String )
      -> (desc : List (EddaRaw INLINE))
      -> EddaRaw INLINE

  Mark : (ty   : MarkupTy)
      -> (text : List (EddaRaw INLINE))
      -> EddaRaw INLINE

  Raw  : (ty   : RawTy)
      -> (verb : String)
      -> EddaRaw INLINE

-- ------------------------------------------------------------------ [ Blocks ]

  HRule : EddaRaw BLOCK
  Empty : EddaRaw BLOCK

  Figure : (label   : Maybe String)
        -> (caption : List (EddaRaw INLINE))
        -> (attrs   : Dict String String)
        -> (link    : EddaRaw INLINE)

        -> EddaRaw BLOCK

  DList : (kvpairs : List (List (EddaRaw INLINE), List (EddaRaw INLINE)))
       -> EddaRaw BLOCK

  Heading : (depth : Nat)
         -> (label : Maybe String)
         -> (title : List (EddaRaw INLINE))
         -> (attrs : Dict String String)
         -> EddaRaw BLOCK

  TextBlock : (ty : TextBlockTy)
           -> (label : Maybe String)
           -> (title : List (EddaRaw INLINE))
           -> (attrs : Dict String String)
           -> (text  : List (EddaRaw INLINE))
           -> EddaRaw BLOCK

  VerbBlock : (ty      : VerbBlockTy)
           -> (label   : Maybe String)
           -> (caption : List (EddaRaw INLINE))
           -> (attrs   : Dict String String)
           -> (content : String)
           -> EddaRaw BLOCK

  ListBlock : (ty : ListTy)
           -> (items : List (List (EddaRaw INLINE)))
           -> EddaRaw BLOCK

  Snippet : (content : List $ EddaRaw a)
         -> (prf : ValidSnippet a)
         -> EddaRaw SNIPPET

  Doc : (title : List (EddaRaw INLINE)) -- @TODO resolve author and dates
     -> (attrs : Dict String String)
     -> (body  : List (EddaRaw BLOCK))
     -> EddaRaw DOC


implementation Show QuoteTy where
  show SQuote = "SQuote"
  show DQuote = "DQuote"

implementation Show CiteSty where
  show ParenSty = "ParenCite"
  show TextSty  = "TextCite"

implementation Show ParenTy where
  show Parents = "Parens"
  show Brackets = "Brackets"
  show Braces = "Braces"

implementation Show FontTy where
  show SerifTy = "Serif"
  show SansTy  = "Sans"
  show ScapTy  = "SmallCaps"
  show MonoTy  = "Monospaced"

implementation Show LinkTy where
  show HyperTy   = "HyperLink"
  show ExposedTy = "Exposed"
  show FnoteTy   = "Footnote"
  show RefTy     = "Internal"
  show CiteTy    = "Citation"

implementation Show MarkupTy where
  show BoldTy   = "Strong"
  show EmphTy   = "Emph"
  show StrikeTy = "Strike"
  show UlineTy  = "Uline"

implementation Show RawTy where
  show VerbTy = "Verb"
  show CodeTy = "Code"
  show MathTy = "Math"

implementation Show TextBlockTy where
  show ParaTy        = "PARAGRAPH"
  show TheoremTy     = "THEOREM"
  show CorollaryTy   = "COROLLARY"
  show LemmaTy       = "LEMMA"
  show PropositionTy = "PROPOSITION"
  show ProofTy       = "PROOF"
  show DefinitionTy  = "DEFINITION"
  show ExampleTy     = "EXAMPLE"
  show ExerciseTy    = "EXERCISE"
  show NoteTy        = "NOTE"
  show ProblemTy     = "PROBLEM"
  show QuestionTy    = "QUESTION"
  show RemarkTy      = "REMARK"
  show SolutionTy    = "SOLUTION"
  show QuotationTy   = "QUOTATION"

implementation Show VerbBlockTy where
  show CommentTy  = "COMMENT"
  show ListingTy  = "LISTING"
  show LiteralTy  = "LITERTAL"
  show EquationTy = "EQUATION"

implementation Show ListTy where
  show BulletTy = "Bullet"
  show NumberTy = "Number"

private
partial
showInline : EddaRaw INLINE -> String
showInline (Punc c)    = unwords ["{Punc", show c,  "}"]
showInline (Font ty t) = unwords ["{Font", show ty, show t, "}"]
showInline (Raw ty t)  = unwords ["{Raw",  show ty, show t, "}"]

showInline (Mark ty ts) = unwords ["{Mark"
                                      , show ty
                                      , concatMap showInline ts
                                      , "}"]

showInline (Link ty u ts) = unwords ["{Link"
                                        , show ty
                                        , "<" ++ u ++ ">"
                                        , show $ concatMap showInline ts
                                        , "}"]



private
partial
showBlock : EddaRaw BLOCK -> String
showBlock (HRule) = "[HRule]"
showBlock (Empty) = "[Empty]"
showBlock (TextBlock ty lab cap as txt) = unwords
    ["[TextBlock"
    , show ty
    , show lab
    , concatMap showInline cap
    , show as
    , concatMap showInline txt
    , "]"]
showBlock (VerbBlock ty lab cap as txt) = unwords
    ["[VerbBlock"
    , show ty
    , show lab
    , concatMap showInline cap
    , show as
    , show txt
    , "]"]
showBlock (ListBlock ty iis) = unwords
    [ "[BList"
    , show ty
    , concatMap (\is => unwords ["[Item", concatMap showInline is, "]"]) iis
    , "]"]
showBlock (Heading d l t a) = unwords
    [ "[Heading"
    , show d
    , show l
    , concatMap showInline t
    , show a
    , "]"]
showBlock (Figure l c as img) = unwords
    [ "[Figure"
    , show l
    , concatMap showInline c
    , show as
    , showInline img
    , "]"]
showBlock (DList ds) = unwords
    [ "[DList"
    , concatMap (\(k,vs) => concatMap showInline k ++ " " ++ concatMap showInline vs) ds
    , "]"]


Show (EddaRaw ty) where
  show x {ty = INLINE} = assert_total $ showInline x
  show x {ty = BLOCK} = assert_total $ showBlock x
  show (Snippet content prf) {ty = SNIPPET} with (prf)
    show (Snippet content prf) {ty = SNIPPET} | IsInLine =
      assert_total $ unwords $ ["[Snippet "] ++ [show content] ++ [" IsInLine]"]
    show (Snippet content prf) {ty = SNIPPET} | IsBlock =
      assert_total $ unwords $ ["[Snippet "] ++ [show content] ++ [" IsBlock]"]

  show (Doc title attrs body) {ty = DOC} =
     assert_total $ unwords $ ["[Doc "] ++ [show title, show attrs, show body] ++ ["]"]
