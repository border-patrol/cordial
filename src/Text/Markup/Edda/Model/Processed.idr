-- --------------------------------------------------------------- [ Model.idr ]
-- Module    : Model.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

module Text.Markup.Edda.Model.Processed

import Data.AVL.Dict

import Text.Markup.Edda.Model.Common

%default total
%access public export

data Edda : EddaTy -> Type where
  Text : String -> Edda INLINE
  Sans : String -> Edda INLINE
  Scap : String -> Edda INLINE
  Mono : String -> Edda INLINE

  Verb : String -> Edda INLINE
  Code : String -> Edda INLINE
  Math : String -> Edda INLINE

  Emph   : List (Edda INLINE) -> Edda INLINE
  Bold   : List (Edda INLINE) -> Edda INLINE
  Strike : List (Edda INLINE) -> Edda INLINE
  Uline  : List (Edda INLINE) -> Edda INLINE

  Quote  : QuoteTy -> List (Edda INLINE) -> Edda INLINE
  Parens : ParenTy -> List (Edda INLINE) -> Edda INLINE

  Ref   : String  -> Edda INLINE
  Cite  : CiteSty -> String -> Edda INLINE
  Hyper : String  -> List (Edda INLINE) -> Edda INLINE
  FNote : String  -> List (Edda INLINE) -> Edda INLINE

  Space      : Edda INLINE
  Newline    : Edda INLINE
  Tab        : Edda INLINE

  Colon      : Edda INLINE
  Semi       : Edda INLINE
  FSlash     : Edda INLINE
  BSlash     : Edda INLINE
  Apostrophe : Edda INLINE
  SMark      : Edda INLINE
  Hyphen     : Edda INLINE
  Comma      : Edda INLINE
  Plus       : Edda INLINE
  Bang       : Edda INLINE
  Period     : Edda INLINE
  QMark      : Edda INLINE
  Hash       : Edda INLINE
  Equals     : Edda INLINE
  Dollar     : Edda INLINE
  Pipe       : Edda INLINE
  Ellipsis   : Edda INLINE
  EmDash     : Edda INLINE
  EnDash     : Edda INLINE

  LAngle     : Edda INLINE
  RAngle     : Edda INLINE

  LBrace     : Edda INLINE
  RBrace     : Edda INLINE

  LParen     : Edda INLINE
  RParen     : Edda INLINE

  LBrack     : Edda INLINE
  RBrack     : Edda INLINE

  MiscPunc   : Char -> Edda INLINE
-- ------------------------------------------------------------------ [ Blocks ]

  HRule : Edda BLOCK
  Empty : Edda BLOCK

  Figure : (label   : Maybe String)
        -> (caption : List (Edda INLINE))
        -> (attrs   : Dict String String)
        -> (url     : Edda INLINE)
        -> Edda BLOCK

  DList : (kvpairs : List (List (Edda INLINE), List (Edda INLINE)))
        -> Edda BLOCK

  Section : (depth : Nat)
         -> (label : Maybe String)
         -> (title : List (Edda INLINE))
         -> (attrs : Dict String String)
         -> (body  : List (Edda BLOCK))
         -> Edda BLOCK

  OList : List (List (Edda INLINE)) -> Edda BLOCK
  BList : List (List (Edda INLINE)) -> Edda BLOCK

  Comment : String -> Edda BLOCK

  Equation : (label : Maybe String) -> (eq : String) -> Edda BLOCK

  Literal : Maybe String
          -> List (Edda INLINE)
          -> String
          -> Edda BLOCK
  Listing : Maybe String
          -> (List (Edda INLINE))
          -> (Maybe String)
          -> (Maybe String)
          -> Dict String String
          -> String
          -> Edda BLOCK

  Para : List (Edda INLINE) -> Edda BLOCK
  Quotation   : Maybe String -> List (Edda INLINE)-> Edda BLOCK

  Theorem     : Maybe String -> List (Edda INLINE) -> List (Edda INLINE) -> Edda BLOCK
  Corollary   : Maybe String -> List (Edda INLINE) -> List (Edda INLINE) -> Edda BLOCK
  Lemma       : Maybe String -> List (Edda INLINE) -> List (Edda INLINE) -> Edda BLOCK
  Proposition : Maybe String -> List (Edda INLINE) -> List (Edda INLINE) -> Edda BLOCK
  Proof       : Maybe String -> List (Edda INLINE) -> List (Edda INLINE) -> Edda BLOCK
  Definition  : Maybe String -> List (Edda INLINE) -> List (Edda INLINE) -> Edda BLOCK
  Exercise    : Maybe String -> List (Edda INLINE) -> List (Edda INLINE) -> Edda BLOCK
  Note        : Maybe String -> List (Edda INLINE) -> List (Edda INLINE) -> Edda BLOCK
  Remark      : Maybe String -> List (Edda INLINE) -> List (Edda INLINE) -> Edda BLOCK
  Problem     : Maybe String -> List (Edda INLINE) -> List (Edda INLINE) -> Edda BLOCK
  Question    : Maybe String -> List (Edda INLINE) -> List (Edda INLINE) -> Edda BLOCK
  Solution    : Maybe String -> List (Edda INLINE) -> List (Edda INLINE) -> Edda BLOCK
  Example     : Maybe String -> List (Edda INLINE) -> List (Edda INLINE) -> Edda BLOCK


  Snippet : (snippet : List $ Edda ty)
         -> (prf : ValidSnippet ty)
         -> Edda SNIPPET

  Doc : (title : List (Edda INLINE))
     -> (attrs : Dict String String)
     -> (body  : List (Edda BLOCK))
     -> Edda DOC

-- --------------------------------------------------------------------- [ EOF ]
