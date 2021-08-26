module Text.Markup.Edda.Process.Inline

import Data.AVL.Dict

import Text.Markup.Edda.Model.Common
import Text.Markup.Edda.Model.Raw
import Text.Markup.Edda.Model.Processed

import Text.Markup.Edda.Process.Squash

%default total
%access private

treatPunc : Char -> Maybe (Edda INLINE)

treatPunc ' '  = Just Space
treatPunc '\n' = Just Newline
treatPunc '\t' = Just Tab
treatPunc '<'  = Just LAngle
treatPunc '>'  = Just RAngle
treatPunc ':'  = Just Colon
treatPunc ';'  = Just Semi
treatPunc '/'  = Just FSlash
treatPunc '\\' = Just BSlash
treatPunc '\'' = Just Apostrophe
treatPunc '-'  = Just Hyphen
treatPunc ','  = Just Comma
treatPunc '+'  = Just Plus
treatPunc '!'  = Just Bang
treatPunc '.'  = Just Period
treatPunc '?'  = Just QMark
treatPunc '#'  = Just Hash
treatPunc '='  = Just Equals
treatPunc '$'  = Just Dollar
treatPunc '|'  = Just Pipe

treatPunc '{' = Just LBrace
treatPunc '}' = Just RBrace
treatPunc '(' = Just LParen
treatPunc ')' = Just RParen
treatPunc '[' = Just LBrack
treatPunc ']' = Just RBrack
treatPunc '"' = Just SMark

treatPunc _  = Nothing

mutual
  refineInline : EddaRaw INLINE -> Edda INLINE

  refineInline (Link RefTy     url desc) = Ref url
  refineInline (Link ExposedTy url desc) = Hyper url Nil
  refineInline (Link HyperTy   url desc) = Hyper url $ refineInlines desc
  refineInline (Link FnoteTy   url desc) = FNote url $ refineInlines desc
  refineInline (Link CiteTy    url desc) = Cite ParenSty url -- <= @TODO

  refineInline (Mark BoldTy   txt) = Bold   $ refineInlines txt
  refineInline (Mark EmphTy   txt) = Emph   $ refineInlines txt
  refineInline (Mark StrikeTy txt) = Strike $ refineInlines txt
  refineInline (Mark UlineTy  txt) = Uline  $ refineInlines txt

  refineInline (Punc c) =
    case treatPunc c of
      Just p  => p
      Nothing => MiscPunc c

  refineInline (Font SerifTy s) = Text s
  refineInline (Font SansTy  s) = Sans s
  refineInline (Font ScapTy  s) = Scap s
  refineInline (Font MonoTy  s) = Mono s

  refineInline (Raw VerbTy v) = Verb v
  refineInline (Raw CodeTy v) = Code v
  refineInline (Raw MathTy v) = Math v

  refineInlines : List (EddaRaw INLINE) -> List (Edda INLINE)
  refineInlines is = map refineInline is

export
process : List (EddaRaw INLINE) -> List (Edda INLINE)
process Nil = Nil
process xs  = squash2 $ squash3 $ refineInlines xs

-- --------------------------------------------------------------------- [ EOF ]
