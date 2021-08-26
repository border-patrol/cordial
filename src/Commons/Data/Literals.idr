-- ------------------------------------------------------------ [ Literals.idr ]
||| Module    : Literals.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
||| Deal with literal values at the type-level.
module Commons.Data.Literals

%default total
%access public export


||| Proof that the given value level `b` of type `ty` has value `a`.
data Literal : (ty : Type)
            -> (a : ty)
            -> Type
  where
    MkLiteral : (b : ty)
             -> (prf : b = a)
             -> Literal ty a

newLiteral : (b : ty) -> Literal ty b
newLiteral b = MkLiteral b Refl

||| Representation of String literals.
LitString : String -> Type
LitString str = Literal String str

||| Proof that the given natural `o` is the successor of `n`.
data Next : (n : Nat) -> Type where
  MkNext : (o : Nat) -> (prf : o = S n) -> Next n

newNext : (o,n : Nat) -> (prf : o = S n) -> Next n
newNext o _ prf = MkNext o prf

-- --------------------------------------------------------------------- [ EOF ]
