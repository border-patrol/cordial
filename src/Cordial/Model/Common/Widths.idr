module Cordial.Model.Common.Widths

import public Data.List
import Data.So

import Commons.Data.Ranged


import Cordial.Model.Common.Essential
import Cordial.Model.Common.Whole
import Cordial.Model.Common.Hacks
import Cordial.Model.Common.WireTy

%default total
%access public export

data CanBeOne : WireTy -> Type where
  ClockIsOne     : CanBeOne (Clock a b c)
  ResetIsOne     : CanBeOne Reset
  InterruptIsOne : CanBeOne Interrupt
  ControlIsOne   : CanBeOne (Control)


data PortWidthDesc : PortShape -> Type where
  UserDefined : PortWidthDesc shape
  One   : PortWidthDesc WIRE
  Width : (w : Whole) -> IsGreaterThanOne w -> PortWidthDesc ARRAY

data HasWidth : PortWidthDesc shape -> Type where
  HasWidthOne : HasWidth One
  HasWidthW : HasWidth (Width w prf)

fromNat : (x : Nat)
       -> {auto prfN : IsSucc x}
       -> (ty ** PortWidthDesc ty)
fromNat x {prfN} with (prfN)
  fromNat (S n) {prfN = prfN} | ItIsSucc with (n)
    fromNat (S n) {prfN = prfN} | ItIsSucc | Z = (WIRE ** One)
    fromNat (S n) {prfN = prfN} | ItIsSucc | (S k) with (isGreaterThanOne $ W (S (S k)) ItIsSucc)
      fromNat (S n) {prfN = prfN} | ItIsSucc | (S k) | (Yes prf) = (ARRAY ** Width (W (S (S k)) ItIsSucc) prf)
      fromNat (S n) {prfN = prfN} | ItIsSucc | (S k) | (No contra) = (WIRE ** One)

namespace Array
  data ValidInt : Int -> Type where
    IsValid : (prfSucc : IsSucc (cast {to=Nat} i))
           -> (prfGT1  : IsGreaterThanOne (W (cast {to=Nat} i) prfSucc))
           -> ValidInt i

  fromInteger : (i : Int)
            -> {auto prf : ValidInt i}
            -> PortWidthDesc ARRAY
  fromInteger i {prf = (IsValid prfSucc prfGT1)} =
    Width (W (cast {to=Nat} i) prfSucc) prfGT1

  fromWhole : (w : Whole)
           -> (prf : IsGreaterThanOne w)
           -> (PortWidthDesc ARRAY)
  fromWhole w prf = Width w prf

  fromNat : (n : Nat)
         -> {auto prfSucc : IsSucc n}
         -> {auto prfGT1  : IsGreaterThanOne (W n prfSucc)}
         -> PortWidthDesc ARRAY
  fromNat n {prfSucc} {prfGT1} = Width (W n prfSucc) prfGT1

  fromDouble : (d : Double)
            -> {auto prfSucc : IsSucc (Hacks.fromDoubleToNat d)}
            -> {auto prfGT1  : IsGreaterThanOne (W (Hacks.fromDoubleToNat d) prfSucc)}
            -> PortWidthDesc ARRAY
  fromDouble d {prfSucc} {prfGT1} = Width (W (Hacks.fromDoubleToNat d) prfSucc) prfGT1

  namespace AtLeastTwo
    fromNat : (n : Nat)
           -> (prfSucc : IsSucc n)
           -> (prfG2 : LTE 2 n)
           -> PortWidthDesc ARRAY
    fromNat (S k) ItIsSucc prfG2 = Width (W (S k) ItIsSucc) (IsGT1 prfG2)

toNat : PortWidthDesc kind -> Nat
toNat UserDefined = 0
toNat One = 1
toNat (Width x _) = toNat x

Cast (PortWidthDesc kind) Nat where
  cast = toNat

Show (PortWidthDesc kind) where
  show UserDefined = show 0
  show One = show 1
  show (Width w x) = show w


namespace Value
  data PortWidth : (shape : PortShape)
                -> (spec  : PortWidthDesc shape)
                -> Type
    where
      One   : PortWidth WIRE One
      Width : (w : Whole)
            -> PortWidth ARRAY (Width w prf)
      UserDef : (w : Whole) -> PortWidth shape UserDefined


  fromNat : (n : Nat)
         -> {auto prfN : IsSucc n}
         -> (spec : PortWidthDesc shape)
         -> PortWidth shape spec
  fromNat n spec {prfN} with (spec)
    fromNat n spec {prfN = prfN} | UserDefined = UserDef (W n prfN)
    fromNat n spec {prfN = prfN} | One = One
    fromNat n spec {prfN = prfN} | (Width w x) = Width w

  fromWhole : (w : Whole)
           -> (spec : PortWidthDesc shape)
           -> PortWidth shape spec
  fromWhole w spec with (spec)
    fromWhole w spec | UserDefined = UserDef w
    fromWhole w spec | One = One
    fromWhole w spec | (Width x y) = Width x


namespace FromArraySpec
  data ValidArraySpec : (w : Nat)
                     -> (ws : List Nat)
                     -> Type
    where
      IsValid : (prfInSet   : Elem w ws)
             -> (prfNotZero : IsSucc w)
             -> (prfNotOne  : IsGreaterThanOne (W w prfNotZero))
             -> ValidArraySpec w ws

  fromNat : (n : Nat)
         -> (prf : ValidArraySpec n ns)
         -> PortWidthDesc ARRAY
  fromNat n {prf = (IsValid prfInSet prfNotZero prfNotOne)} =
     Width (W n prfNotZero) prfNotOne


  widthIsZero : (contra : IsSucc w -> Void) -> ValidArraySpec w ws -> Void
  widthIsZero contra (IsValid prfInSet prfNotZero prfNotOne) = contra prfNotZero

  widthNotInList : (contra : Elem w ws -> Void) -> ValidArraySpec w ws -> Void
  widthNotInList contra (IsValid prfInSet prfNotZero prfNotOne) = contra prfInSet

  widthIsOne : (contra : IsGreaterThanOne (W (S n) ItIsSucc) -> Void) -> ValidArraySpec (S n) ws -> Void
  widthIsOne contra (IsValid prfInSet ItIsSucc (IsGT1 x)) = contra (IsGT1 x)

  validArraySpec : (w : Nat) -> (ws : List Nat)
                -> Dec (ValidArraySpec w ws)
  validArraySpec w ws with (isItSucc w)
    validArraySpec w ws | (Yes prf) with (isGreaterThanOne (W w prf))
      validArraySpec w ws | (Yes prf) | (Yes x) with (isElem w ws)
        validArraySpec w ws | (Yes prf) | (Yes x) | (Yes y) = Yes (IsValid y prf x)
        validArraySpec w ws | (Yes prf) | (Yes x) | (No contra) = No (widthNotInList contra)

      validArraySpec (S n) ws | (Yes ItIsSucc) | (No contra) = No (widthIsOne contra)

    validArraySpec w ws | (No contra) = No (widthIsZero contra)

   namespace Hint
     %hint
     validArraySpec : (w : Nat) -> (ws : List Nat)
                   -> {auto prfElem : Elem w ws}
                   -> {auto prfSucc : IsSucc w}
                   -> {auto prfGT1  : IsGreaterThanOne (W w prfSucc)}
                   -> ValidArraySpec w ws
     validArraySpec w ws {prfElem} {prfSucc} {prfGT1} = IsValid prfElem prfSucc prfGT1

namespace FromDouble
   fromDouble : (d : Double)
             -> (shape ** PortWidthDesc shape)
   fromDouble d with (fromDoubleToNat d)
     fromDouble d | Z = (WIRE ** One)
     fromDouble d | (S k) = (WIRE ** One)
     fromDouble d | (S (S k)) = fromNat (S (S k)) {prfN=ItIsSucc}


{-
  fromDouble : (d : Double)
            -> {auto prfSucc : IsSucc (fromDoubleToNat d)}
            -> {auto prfGT1  : IsGreaterThanOne (W (fromDoubleToNat d) prfSucc)}
            -> PortWidthDesc ARRAY
  fromDouble d {prfSucc} {prfGT1} = Width (W (fromDoubleToNat d) prfSucc) prfGT1

-}
-- --------------------------------------------------------------------- [ EOF ]
