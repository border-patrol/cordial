module Cordial.Model.Common.Hacks

%default total
%access public export


fromDoubleToNat : Double -> Nat
fromDoubleToNat x =
  let x_int = cast {to=Int} x
  in cast {to=Nat} x_int

calcBits : Double -> Double
calcBits d = (ceiling ((log (d / 8)) / (log 2))) - 1
