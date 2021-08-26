module Commons.Data.Rig

import public Data.Vect

%default total
%access public export

data TyRig = None | One | Tonne

noneNotOne : (None = One) -> Void
noneNotOne Refl impossible

noneNotTonne : (None = Tonne) -> Void
noneNotTonne Refl impossible

oneNotTonne : (One = Tonne) -> Void
oneNotTonne Refl impossible

DecEq TyRig where
  decEq None None = Yes Refl
  decEq None One = No noneNotOne
  decEq None Tonne = No noneNotTonne
  decEq One None = No (negEqSym noneNotOne)
  decEq One One = Yes Refl
  decEq One Tonne = No oneNotTonne
  decEq Tonne None = No (negEqSym noneNotTonne)
  decEq Tonne One = No (negEqSym oneNotTonne)
  decEq Tonne Tonne = Yes Refl


export
plus : TyRig -> TyRig -> TyRig
plus None None = None
plus None One = One
plus None Tonne = Tonne
plus One None = One
plus One One = Tonne
plus One Tonne = Tonne
plus Tonne None = Tonne
plus Tonne One = Tonne
plus Tonne Tonne = Tonne

export
multiply : TyRig -> TyRig -> TyRig
multiply None None = None
multiply None One = None
multiply None Tonne = None
multiply One None = None
multiply One One = One
multiply One Tonne = Tonne
multiply Tonne None = None
multiply Tonne One = Tonne
multiply Tonne Tonne = Tonne

export
product : Vect n TyRig -> Vect n TyRig -> Vect n TyRig
product [] [] = []
product (x :: xs) (y :: ys) = multiply x y :: product xs ys

export
sum : Vect n TyRig -> Vect n TyRig -> Vect n TyRig
sum [] [] = []
sum (x :: xs) (y :: ys) = plus x y :: sum xs ys
