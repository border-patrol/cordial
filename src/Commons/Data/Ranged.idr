-- -------------------------------------------------------------- [ Ranges.idr ]
||| Module    : Ranges.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
|||
module Commons.Data.Ranged

import Data.So

%access export
%default total

namespace Int

  data IntRange : (l,u : Int)
               -> (prf : So (l < u))
               -> Type where
    MkIntRange : (l,u : Int) -> (prf : So (l < u)) -> IntRange l u prf

  mkIntRange : (l,u : Int)
         -> {auto prf : So (l < u)}
         -> IntRange l u prf
  mkIntRange l u {prf} = MkIntRange l u prf

  data RangedInt : (lower : Int)
                -> (upper : Int)
                -> Type
    where
      MkRangedInt : (x     : Int)
                 -> (range : IntRange l u vrange)
                 -> (prf   : So (l <= x && x <= u))
                 -> RangedInt l u

  getValue : RangedInt l u -> Int
  getValue (MkRangedInt x _ _) = x

  getRange : RangedInt l u -> (Int, Int)
  getRange (MkRangedInt _ (MkIntRange l u _) _) = (l, u)

  inRange : (x : Int)
         -> (range : IntRange l u prf)
         -> Maybe (RangedInt l u)
  inRange x range with (choose $ l <= x && x <= u)
    inRange x range | (Left  okay) = Just $ MkRangedInt x range okay
    inRange x range | (Right nout) = Nothing

  Show (IntRange l u prf) where
    show (MkIntRange l u _) = unwords ["(", show l, ",", show u, ")"]

  Show (RangedInt l u) where
    show (MkRangedInt x (MkIntRange l u _) _) = unwords ["(", show l, "<=", show x, "<=", show u, ")"]

namespace Nat

  data NatRange : (l,u : Nat)
               -> (prf : LT l u)
               -> Type
    where
      MkNatRange : (l,u : Nat) -> (prf : LT l u) -> NatRange l u prf

  mkNatRange : (l,u : Nat) -> {auto prf : LT l u} -> NatRange l u prf
  mkNatRange l u {prf} = MkNatRange l u prf

  data RangedNat : (lower : Nat)
                -> (upper : Nat)
                -> Type where
    MkRangedNat : (x : Nat)
               -> (range : NatRange l u prfRange)
               -> (prfLower : LTE l x)
               -> (prfUpper : LTE x u)
               -> RangedNat l u

  getValue : RangedNat l u -> Nat
  getValue (MkRangedNat x _ _ _) = x

  getRange : RangedNat l u -> (Nat, Nat)
  getRange (MkRangedNat _ (MkNatRange l u _) _ _) = (l, u)

  inRange : (x : Nat)
         -> (range : NatRange l u prf)
         -> Maybe $ RangedNat l u
  inRange x (MkNatRange l u prf) with (isLTE l x)
    inRange x (MkNatRange l u prf) | (Yes y) with (isLTE x u)
      inRange x (MkNatRange l u prf) | (Yes y) | (Yes z) = Just (MkRangedNat x (MkNatRange l u prf) y z)
      inRange x (MkNatRange l u prf) | (Yes y) | (No contra) = Nothing
    inRange x (MkNatRange l u prf) | (No contra) = Nothing

  Show (NatRange l u prf) where
    show (MkNatRange l u prf) = unwords ["(", show l, ",", show u, ")"]

  Show (RangedNat l u) where
    show (MkRangedNat x (MkNatRange l u prf) _ _) = unwords ["(", show l, "<=", show x, "<=", show u, ")"]


-- --------------------------------------------------------------------- [ EOF ]
