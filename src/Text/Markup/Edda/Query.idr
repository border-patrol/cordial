module Text.Markup.Edda.Query

import Data.AVL.Dict

import Text.Markup.Edda.Model.Common
import Text.Markup.Edda.Model.Raw
import Text.Markup.Edda.Model.Processed

%access export

interface Queryable a b where
  query : Monoid res => (a -> res) -> b -> res

Queryable a b => Queryable a (List b) where
  query f xs = foldr (<+>) neutral $ map (query f) xs

(Queryable a b, Queryable a c) => Queryable a (b,c) where
  query f (x,y) = (query f x) <+> (query f y)

Queryable (Edda INLINE) (Edda INLINE) where
  -- INLINE -> INLINE
  query f (Emph xs)   = f (Emph xs) <+> (query f xs)
  query f (Bold xs)   = f (Bold xs) <+> (query f xs)
  query f (Strike xs) = f (Strike xs) <+> (query f xs)
  query f (Uline xs)  = f (Uline xs) <+> (query f xs)

  query f (Quote ty xs)  = f (Quote ty xs) <+> (query f xs)
  query f (Parens ty xs) = f (Parens ty xs) <+> (query f xs)

  query f (Hyper l xs)  = f (Hyper l xs) <+> (query f xs)
  query f (FNote l xs)  = f (FNote l xs) <+> (query f xs)
  query f inline  = f inline

Queryable (Edda INLINE) (Edda BLOCK) where
  -- INLINE to BLOCK
  query f (Section d l t as bs) = query f t <+> query f bs
  query f (Figure l c as fig) = query f c <+> query f fig
  query f (DList kvs)         = query f kvs

  query f (OList xs)  = query f xs
  query f (BList xs)  = query f xs

  query f (Literal l c ss)      = neutral <+> query f c
  query f (Listing l c ty ops as s) = neutral <+> query f c

  query f (Para xs)        = query f xs
  query f (Quotation l xs) = query f xs

  query f (Theorem l c xs)     = query f xs <+> query f c
  query f (Corollary l c xs)   = query f xs <+> query f c
  query f (Lemma l c xs)       = query f xs <+> query f c
  query f (Proposition l c xs) = query f xs <+> query f c
  query f (Proof l c xs)       = query f xs <+> query f c
  query f (Definition l c xs)  = query f xs <+> query f c
  query f (Exercise l c xs)    = query f xs <+> query f c
  query f (Note l c xs)        = query f xs <+> query f c
  query f (Remark l c xs)      = query f xs <+> query f c
  query f (Problem l c xs)     = query f xs <+> query f c
  query f (Question l c xs)    = query f xs <+> query f c
  query f (Solution l c xs)    = query f xs <+> query f c
  query f (Example l c xs)     = query f xs <+> query f c
  query f block = neutral

Queryable (Edda BLOCK) (Edda INLINE) where
  -- BLOCK to INLINE

  query f (Emph xs)   = query f xs
  query f (Bold xs)   = query f xs
  query f (Strike xs) = query f xs
  query f (Uline xs)  = query f xs

  query f (Quote ty xs)  = query f xs
  query f (Parens ty xs) = query f xs

  query f (Ref l)      = neutral
  query f (Cite ty l)  = neutral
  query f (Hyper l xs) = neutral <+> query f xs
  query f (FNote l xs) = neutral <+> query f xs
  query f (MiscPunc c) = neutral

  query f inline = neutral

Queryable (Edda BLOCK) (Edda BLOCK) where
  -- BLOCK to BLOCK
  query f (Section d l t as bs) = f (Section d l t as bs) <+> (query f t) <+> query f bs
  query f (Figure l c as fig)   = f (Figure l c as fig) <+> (query f fig) <+> query f c
  query f (DList kvs)           = f (DList kvs) <+> (query f kvs)

  query f (OList xs)  = f (OList xs) <+> (query f xs)
  query f (BList xs)  = f (BList xs) <+> (query f xs)

  query f (Literal l c ss)      = f (Literal l c ss) <+> query f c
  query f (Listing l c ty ops as s) = f (Listing l c ty ops as s) <+> query f c

  query f (Para xs)        = f (Para xs) <+> query f xs
  query f (Quotation l xs) = f (Quotation l xs) <+> (query f xs)

  query f (Theorem l c xs)     = f (Theorem l c xs) <+> (query f xs) <+> query f c
  query f (Corollary l c xs)   = f (Corollary l c xs) <+> (query f xs) <+> query f c
  query f (Lemma l c xs)       = f (Lemma l c xs) <+> (query f xs) <+> query f c
  query f (Proposition l c xs) = f (Proposition l c xs) <+> (query f xs) <+> query f c
  query f (Proof l c xs)       = f (Proof l c xs) <+> (query f xs) <+> query f c
  query f (Definition l c xs)  = f (Definition l c xs) <+> (query f xs) <+> query f c
  query f (Exercise l c xs)    = f (Exercise l c xs) <+> (query f xs) <+> query f c
  query f (Note l c xs)        = f (Note l c xs) <+> (query f xs) <+> query f c
  query f (Remark l c xs)      = f (Remark l c xs) <+> (query f xs) <+> query f c
  query f (Problem l c xs)     = f (Problem l c xs) <+> (query f xs) <+> query f c
  query f (Question l c xs)    = f (Question l c xs) <+> (query f xs) <+> query f c
  query f (Solution l c xs)    = f (Solution l c xs) <+> (query f xs) <+> query f c
  query f (Example l c xs)     = f (Example l c xs) <+> (query f xs) <+> query f c

  query f block = f block

Queryable (Edda BLOCK) (Edda DOC) where
  -- BLOCK to DOC
  query f (Doc t as body) = query f body

Queryable (Edda INLINE) (Edda DOC) where
  -- INLINE to DOC
  query f (Doc t as body) = query f body

  -- DOC tp DOC
Queryable (Edda DOC) (Edda DOC) where
  query f doc = f doc


Queryable (Edda BLOCK) (Edda SNIPPET) where
  -- BLOCK to SNIPPET
  query f (Snippet snippet prf) with (prf)
    query f (Snippet snippet prf) | IsInLine = query f snippet
    query f (Snippet snippet prf) | IsBlock = query f snippet

Queryable (Edda INLINE) (Edda SNIPPET) where
  -- INLINE to SNIPPET
  query f (Snippet snippet prf) with (prf)
    query f (Snippet snippet prf) | IsInLine = query f snippet
    query f (Snippet snippet prf) | IsBlock = query f snippet


Queryable (Edda SNIPPET) (Edda SNIPPET) where
  -- snippet to snippet
  query f snip = f snip

-- --------------------------------------------------------------------- [ EOF ]
