module Cordial.Model.Interface.PortViews

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

data Necessary : (ty : OptTy)
              -> (endpoint : Endpoint)
              -> (optTy : OptionalTy)
              -> (prf : OptionalKind endpoint optTy ty)
              -> Type

-}

data SimplePort : Necessary ty endpoint opt prf -> Type where
  MkSimplePort : (type : PortTy annot labelTy)
              -> (pType : ProjectedPortTy labelTy endpoint type)
              -> (port : Port annot
                               labelTy
                               req
                               endpoint
                               endian
                               type
                               ptype)
              -> SimplePort req


data SimplePortGroup : Type where
   Empty : SimplePortGroup
   Add : (port : SimplePort req) -> (rest : SimplePortGroup) -> SimplePortGroup
   Skip : (rest : SimplePortGroup) -> SimplePortGroup

mkSimple : PortGroup annot labelTy endpoint endian ps pps
        -> SimplePortGroup
mkSimple Empty = Empty
mkSimple (Add port rest) = Add (MkSimplePort port) (mkSimple rest)
mkSimple (Skip rest) = Skip (mkSimple rest)

{-


||| A collection of ports that respects the projected port group.
|||
||| Universe that logical names arise from.
||| Are we producing/consuming information.
||| The originating projected port type that constrains the value level values.
|||
data PortGroup : (annot    : Type)
              -> (labelTy    : Type)
              -> (endpoint : Endpoint)
              -> (endian   : Maybe Endian)
              -> (ps       : PortGroupTy annot labelTy)
              -> (pportTys : DList (PortTy annot labelTy) (ProjectedPortTy labelTy endpoint) ps)
              -> Type
  where
    ||| No ports
    Empty : PortGroup annot labelTy endpoint endian Nil Nil

    ||| Add a port to the group such that the description comes from
    ||| the projected port list.
    Add  : (port : Port annot labelTy req endpoint endian (PortDesc  i k l ty f dw sen opt origin dv doc)
                                                          (PPortDesc   k l ty d dw sen req origin dv))
        -> (rest : PortGroup annot labelTy endpoint endian ps pps)
        -> PortGroup annot labelTy endpoint endian (PortDesc  i k l ty f dw sen opt origin dv doc :: ps)
                                                   (PPortDesc   k l ty d dw sen req origin dv     :: pps)

    ||| Skip an optional port from the projected port list.
    Skip : (rest : PortGroup annot labelTy endpoint endian ps pps)
        -> PortGroup annot labelTy endpoint endian (PortDesc  i k l ty f dw sen opt      origin dv doc :: ps)
                                                 (PPortDesc   k l ty d dw sen Optional origin dv     :: pps)

-}
-- --------------------------------------------------------------------- [ EOF ]
