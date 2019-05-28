module Cordial.Model.Interface.PortGroup.Views

import Data.Vect
import Data.DList
import Data.Ranged

import Text.Markup.Edda

import Cordial.Model.Common
import Cordial.Model.Specification
import Cordial.Model.Projection

import Cordial.Model.Interface.Kinds
import Cordial.Model.Interface.Ports
import Cordial.Model.Interface.PortGroup

%default total
%access public export

{-

data PortGroup : (annot    : Type)
              -> (labelTy    : Type)
              -> (endpoint : Endpoint)
              -> (endian   : Maybe Endian)
              -> (ps       : PortGroupTy annot labelTy)
              -> (pportTys : DList (PortTy annot labelTy) (ProjectedPortTy labelTy endpoint) ps)
              -> Type
  where

-}
namespace System
  data SystemPortGroup : (portGroup : PortGroup annot labelTy endpoint endian types projectedTypes)
                      -> Type
    where
      Empty : SystemPortGroup Empty
      Add : (port : Port annot labelTy type projectedType endpoint endian)
         -> (prf  : SystemPort port)
         -> (rest : SystemPortGroup ports)
         -> SystemPortGroup (Add port ports)

      NotSystemPort : (prf : SystemPort port -> Void)
                   -> (rest : SystemPortGroup ports)
                   -> SystemPortGroup (Add port ports)
      Skip : (rest : SystemPortGroup ports)
          -> SystemPortGroup (Skip ports prf)

  toSystemPortGroup : (portGroup : PortGroup annot labelTy endpoint endian types projectedTypes)
                   -> SystemPortGroup portGroup
  toSystemPortGroup Empty = Empty
  toSystemPortGroup (Add port rest {projectedType} {type}) with (isProjectedPortSystem projectedType)
    toSystemPortGroup (Add port rest {projectedType = projectedType} {type = type}) | (Yes prf) = Add port (PortIsSystem prf) (toSystemPortGroup rest)
    toSystemPortGroup (Add port rest {projectedType = projectedType} {type = type}) | (No contra) = NotSystemPort (contra) (toSystemPortGroup rest)

  toSystemPortGroup (Skip rest prf) = Skip (toSystemPortGroup rest)
