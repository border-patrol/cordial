module Text.Markup.Edda.Process.BLock

import Data.AVL.Dict

import Text.Markup.Edda.Model.Common
import Text.Markup.Edda.Model.Raw
import Text.Markup.Edda.Model.Processed

import Text.Markup.Edda.Process.Inline
import Text.Markup.Edda.Process.Squash
import Text.Markup.Edda.Process.Shunt
import Text.Markup.Edda.Process.Utils

%default covering
%access private

-- ----------------------------------------------------------- [ Refine Blocks ]

mutual

  refineBlock : EddaRaw BLOCK -> Edda BLOCK
  refineBlock HRule = HRule

  refineBlock Empty = Empty

  refineBlock (Heading d l t as) = Section d l (process t) as Nil

  refineBlock (Figure l c as img) =
      Figure l (process c) as url
    where
       url = case process [img] of
               Nil => Text "Shouldn't happen"
               (res::_) => res


  refineBlock (DList kvs) = DList $ map (\(k, vs) => (process k, process vs)) kvs

  refineBlock (TextBlock ParaTy        l c as t) = Para (process t)
  refineBlock (TextBlock QuotationTy   l c as t) = Quotation   l (process t)
  refineBlock (TextBlock TheoremTy     l c as t) = Theorem     l (process c) (process t)
  refineBlock (TextBlock CorollaryTy   l c as t) = Corollary   l (process c) (process t)
  refineBlock (TextBlock LemmaTy       l c as t) = Lemma       l (process c) (process t)
  refineBlock (TextBlock PropositionTy l c as t) = Proposition l (process c) (process t)
  refineBlock (TextBlock ProofTy       l c as t) = Proof       l (process c) (process t)
  refineBlock (TextBlock DefinitionTy  l c as t) = Definition  l (process c) (process t)
  refineBlock (TextBlock ExerciseTy    l c as t) = Exercise    l (process c) (process t)
  refineBlock (TextBlock NoteTy        l c as t) = Note        l (process c) (process t)
  refineBlock (TextBlock ProblemTy     l c as t) = Problem     l (process c) (process t)
  refineBlock (TextBlock QuestionTy    l c as t) = Question    l (process c) (process t)
  refineBlock (TextBlock RemarkTy      l c as t) = Remark      l (process c) (process t)
  refineBlock (TextBlock SolutionTy    l c as t) = Solution    l (process c) (process t)
  refineBlock (TextBlock ExampleTy     l c as t) = Example     l (process c) (process t)

  refineBlock (VerbBlock CommentTy l c as s) = Comment s
  refineBlock (VerbBlock ListingTy l c as s) = Listing l (process c)
                                                         (lookupSrcLang as)
                                                         (lookupSrcOpts as)
                                                         ((nubAttribute "src_lang" $ nubAttribute "src_opts" as))
                                                         s
  refineBlock (VerbBlock LiteralTy  l c as s) = Literal l (process c) s
  refineBlock (VerbBlock EquationTy l c as s) = Equation l s

  refineBlock (ListBlock NumberTy bs) = OList $ map process bs
  refineBlock (ListBlock BulletTy bs) = BList $ map process bs

  refineBlocks : List (EddaRaw BLOCK) -> List (Edda BLOCK)
  refineBlocks = map refineBlock


export
process : List (EddaRaw BLOCK) -> List (Edda BLOCK)
process = shunt . squash2 . refineBlocks
