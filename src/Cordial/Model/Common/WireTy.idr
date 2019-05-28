module Cordial.Model.Common.WireTy

import Data.Ranged

import Cordial.Model.Common.Essential

%default total
%access public export

||| Type of wire.
data WireTy : Type where
   ||| Does the wire carry memory mapable data or addresses
   Data : Bool -> WireTy

   ||| Clock for the interface
   Clock : (edge  : Maybe ClockEdge)
        -> (delay : Maybe Delay)
        -> (phase : Maybe (RangedNat 0 100))
        -> WireTy

   Reset : WireTy

   Information : WireTy
   Interrupt : WireTy
   Control   : WireTy
   General   : WireTy

DataWire : WireTy
DataWire = Data False

AddressWire : WireTy
AddressWire = Data True
