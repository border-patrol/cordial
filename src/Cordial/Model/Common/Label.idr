module Cordial.Model.Common.Label

%default total
%access public export

data LabelKind = ANY | NAMED | INDEXED

||| Named labels for signals.
|||
||| @kind   The kind of label.
||| @ty The type associated with each label.
data Label : (kind : LabelKind) -> (ty : Type) -> Type where
  ||| Represents 'Any' label.
  A : Label ANY ty
  ||| Represents a 'Named' label.
  N : ty -> Label NAMED ty
  ||| Represents an indexed 'Named' label.
  I : ty -> Nat -> Label INDEXED ty

Show rTy => Show (Label kind rTy) where
  show A       = "any"
  show (N x)   = show x
  show (I x k) = show x <+> "_" <+> show k
