module Text.Markup.Edda.Walk

import Data.AVL.Dict

import Text.Markup.Edda.Model.Common
import Text.Markup.Edda.Model.Raw
import Text.Markup.Edda.Model.Processed

%access export

interface Walkable a z where
  walk : (a -> a) -> z -> z

Walkable a b => Walkable a (List b) where
  walk f xs = map (walk f) xs

(Walkable a b, Walkable a c) => Walkable a (b,c) where
  walk f (x,y) = (walk f x, walk f y)


Walkable (Edda INLINE) (Edda INLINE) where
  -- inline to inline
  walk f (Emph xs)   = f $ Emph (walk f xs)
  walk f (Bold xs)   = f $ Bold (walk f xs)
  walk f (Strike xs) = f $ Strike (walk f xs)
  walk f (Uline xs)  = f $ Uline (walk f xs)

  walk f (Quote ty xs)  = f $ Quote ty (walk f xs)
  walk f (Parens ty xs) = f $ Parens ty (walk f xs)

  walk f (Ref uri)        = f $ Ref uri
  walk f (Cite ty uri)    = f $ Cite ty uri
  walk f (Hyper uri desc) = f $ Hyper uri (walk f desc)
  walk f (FNote uri desc) = f $ FNote uri (walk f desc)
  walk f (MiscPunc c)     = f $ MiscPunc c

  walk f inline = f inline

Walkable (Edda INLINE) (Edda BLOCK) where
  -- Inline structures from Blocks
  walk f (Section d l t as bs) = Section d l (walk f t) as (walk f bs)
  walk f (Figure l c as fig)   = Figure l (walk f c) as (walk f fig)
  walk f (DList kvs)           = DList (walk f kvs)

  walk f (OList xs) = OList (walk f xs)
  walk f (BList xs) = BList (walk f xs)

  walk f (Literal l c ss)       = Literal l (walk f c) ss
  walk f (Listing l c ty ops as s)  = Listing l (walk f c) ty ops as s

  walk f (Para xs)        = Para $ walk f xs
  walk f (Quotation l xs) = Quotation l (walk f xs)

  walk f (Theorem l c xs)     = Theorem l (walk f c) (walk f xs)
  walk f (Corollary l c xs)   = Corollary l (walk f c) (walk f xs)
  walk f (Lemma l c xs)       = Lemma l (walk f c) (walk f xs)
  walk f (Proposition l c xs) = Proposition l (walk f c) (walk f xs)
  walk f (Proof l c xs)       = Proof l (walk f c) (walk f xs)
  walk f (Definition l c xs)  = Definition l (walk f c) (walk f xs)
  walk f (Exercise l c xs)    = Exercise l (walk f c) (walk f xs)
  walk f (Note l c xs)        = Note l (walk f c) (walk f xs)
  walk f (Remark l c xs)      = Remark l (walk f c) (walk f xs)
  walk f (Problem l c xs)     = Problem l (walk f c) (walk f xs)
  walk f (Question l c xs)    = Question l (walk f c) (walk f xs)
  walk f (Solution l c xs)    = Solution l (walk f c) (walk f xs)
  walk f (Example l c xs)     = Example l (walk f c) (walk f xs)

  walk f block = block

Walkable (Edda BLOCK) (Edda INLINE) where
  walk  f (Emph xs)   = Emph (walk f xs)
  walk  f (Bold xs)   = Bold (walk f xs)
  walk  f (Strike xs) = Strike (walk f xs)
  walk  f (Uline xs)  = Uline (walk f xs)

  walk  f (Quote ty xs)  = Quote ty (walk f xs)
  walk  f (Parens ty xs) = Parens ty (walk f xs)

  walk  f (Hyper l xs) = Hyper l (walk f xs)
  walk  f (FNote l xs) = FNote l (walk f xs)
  walk  f inline = inline

Walkable (Edda BLOCK) (Edda BLOCK) where
  -- Walk Block structures from Blocks
  walk  f (Section d l t as bs)  = f $ Section d l (walk f t) as (walk f bs)
  walk  f (Figure l c as fig) = f $ Figure l (walk f c) as (walk f fig)
  walk  f (DList kvs)         = f $ DList (walk f kvs)

  walk  f (OList xs)  = f $ OList (walk f xs)
  walk  f (BList xs)  = f $ BList (walk f xs)

  walk  f (Para xs)           = f $ Para $ walk f xs
  walk  f (Quotation l xs)    = f $ Quotation l (walk f xs)

  walk  f (Theorem l c xs)     = f $ Theorem l c (walk f xs)
  walk  f (Corollary l c xs)   = f $ Corollary l c (walk f xs)
  walk  f (Lemma l c xs)       = f $ Lemma l c (walk f xs)
  walk  f (Proposition l c xs) = f $ Proposition l c (walk f xs)
  walk  f (Proof l c xs)       = f $ Proof l c (walk f xs)
  walk  f (Definition l c xs)  = f $ Definition l c (walk f xs)
  walk  f (Exercise l c xs)    = f $ Exercise l c (walk f xs)
  walk  f (Note l c xs)        = f $ Note l c (walk f xs)
  walk  f (Remark l c xs)      = f $ Remark l c (walk f xs)
  walk  f (Problem l c xs)     = f $ Problem l c (walk f xs)
  walk  f (Question l c xs)    = f $ Question l c (walk f xs)
  walk  f (Solution l c xs)    = f $ Solution l c (walk f xs)
  walk  f (Example l c xs)     = f $ Example l c (walk f xs)

  walk  f block  = f block

Walkable (Edda BLOCK) (Edda DOC) where
  -- Walk block structures from Doc
  walk f (Doc t as bs) = Doc t as (walk f bs)


Walkable (Edda INLINE) (Edda DOC) where
  -- Walk Inline structures from Doc
  walk f (Doc t as bs) = Doc (walk f t) as (walk f bs)

Walkable (Edda DOC) (Edda DOC) where
  -- Walk the doc
  walk f x = f x

Walkable (Edda BLOCK) (Edda SNIPPET) where
  -- Walk block structures from Doc
  walk f (Snippet snippet prf) with (prf)
    walk f (Snippet snippet prf) | IsInLine = Snippet (walk f snippet) prf
    walk f (Snippet snippet prf) | IsBlock = Snippet (walk f snippet) prf


  -- Snippet (map (walk f) ss) prf

Walkable (Edda INLINE) (Edda SNIPPET) where
  -- Walk Inline structures from Doc
  walk f (Snippet snippet prf) with (prf)
    walk f (Snippet snippet prf) | IsInLine = Snippet (walk f snippet) prf
    walk f (Snippet snippet prf) | IsBlock = Snippet (walk f snippet) prf

--  walk f (Snippet ss prf) = Snippet (map (walk f {z=INLINE}) ss) prf

Walkable (Edda SNIPPET) (Edda SNIPPET) where
  -- Walk the doc
  walk f x = f x

-- --------------------------------------------------------------------- [ EOF ]
