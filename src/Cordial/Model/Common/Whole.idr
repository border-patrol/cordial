module Cordial.Model.Common.Whole

%default total
%access public export


data Whole : Type where
  W : (n : Nat) -> (prf : IsSucc n) -> Whole

data IsOne : Whole -> Type where
  ItIsOne : IsOne (W (S Z) ItIsSucc)

wholeIsNotOne : Not (IsOne $ W (S (S n)) ItIsSucc)
wholeIsNotOne ItIsOne impossible

isOne : (w : Whole) -> Dec (IsOne w)
isOne (W n prf) with (prf)
  isOne (W (S k) prf) | ItIsSucc with (k)
    isOne (W (S k) prf) | ItIsSucc | Z = Yes ItIsOne
    isOne (W (S k) prf) | ItIsSucc | (S j) = No wholeIsNotOne


data IsGreaterThanOne : Whole -> Type where
  IsGT1 : (LTE 2 (S n)) -> IsGreaterThanOne (W (S n) ItIsSucc)

wholeIsOne : Not (IsGreaterThanOne $ W (S Z) ItIsSucc)
wholeIsOne (IsGT1 (LTESucc LTEZero)) impossible
wholeIsOne (IsGT1 (LTESucc (LTESucc _))) impossible

decEqWholeNotEqual : (contra : (k = j) -> Void) -> (W (S k) ItIsSucc = W (S j) ItIsSucc) -> Void
decEqWholeNotEqual contra Refl = contra Refl

isGreaterThanOne : (w : Whole) -> Dec (IsGreaterThanOne w)
isGreaterThanOne (W n prf) with (prf)
  isGreaterThanOne (W (S k) prf) | ItIsSucc with (isLTE 2 (S k))
    isGreaterThanOne (W (S k) prf) | ItIsSucc | (Yes x) = Yes (IsGT1 x)
    isGreaterThanOne (W (S k) prf) | ItIsSucc | (No contra) with (k)
      isGreaterThanOne (W (S k) prf) | ItIsSucc | (No contra) | Z = No wholeIsOne
      isGreaterThanOne (W (S k) prf) | ItIsSucc | (No contra) | (S j) = Yes (IsGT1 (LTESucc (LTESucc LTEZero)))


DecEq Whole where
  decEq (W (S k) ItIsSucc) (W (S j) ItIsSucc) with (decEq k j)
    decEq (W (S j) ItIsSucc) (W (S j) ItIsSucc) | (Yes Refl) = Yes Refl
    decEq (W (S k) ItIsSucc) (W (S j) ItIsSucc) | (No contra) = No (decEqWholeNotEqual contra)


toNat : Whole -> Nat
toNat (W n prf) = n


fromNat : (x : Nat) -> {auto prf : IsSucc x} -> Whole
fromNat x {prf} = W x prf

data LTE : Whole -> Whole -> Type where
  IsLTE : (prf : LTE min max)
       -> LTE (W min prfA) (W mac prfB)

Show Whole where
  show (W n prf) = show n

Eq Whole where
  (W l prfL) == (W r prfR) = l == r

Cast Whole Integer where
  cast (W w prf) = toIntegerNat w

Ord Whole where
  compare (W l prfL) (W r prfR) = compare l r
