module Cordial.Model.Interface.Kinds

import Data.Vect
import Data.DList
import Data.Ranged

import Text.Markup.Edda

import Cordial.Model.Common
import Cordial.Model.Specification
import Cordial.Model.Projection

%default total
%access public export


||| What type of interface are we.
data InterfaceKind : (isMonitor : Bool)
                  -> (endpoint  : Endpoint)
                  -> Type
  where
    Producer  : InterfaceKind False PRODUCER
    Consumer  : InterfaceKind False CONSUMER

    System   : (e : Endpoint) -> InterfaceKind False e

    Monitor  : InterfaceKind True CONSUMER

namespace IKinds

   data InterfaceKinds : List (Bool, Endpoint) -> Type where
      Nil : InterfaceKinds Nil
      (::) : InterfaceKind b e
          -> InterfaceKinds kinds
          -> InterfaceKinds ((b,e)::kinds)


   {- [ NOTE ]

   I would rather replace `InterfaceKinds` with a DList. However, type
   checking later on becomes problematic. Idris, for some reason,
   cannot resolve the types.

   -}
