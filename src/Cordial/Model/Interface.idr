-- ----------------------------------------------------------- [ Interface.idr ]
-- Module    : Interface.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| Description of an interface as used by an IP Core.
module Cordial.Model.Interface

import Data.Vect
import Data.DList
import Data.Ranged

import Text.Markup.Edda

import public Cordial.Model.Common
import        Cordial.Model.Specification
import public Cordial.Model.Projection

import public Cordial.Model.Interface.Kinds
import public Cordial.Model.Interface.Ports
import public Cordial.Model.Interface.PortGroup

%default total
%access public export

||| Data type representing the physical port.
data Interface : (annot          : Type)
              -> (labelTy        : Type)
              -> (endpoint       : Endpoint)
              -> (kind           : InterfaceKind isMonitor endpoint)
              -> (endian         : Maybe Endian)
              -> (interfaceTy    : InterfaceTy annot labelTy)
              -> (pinterfaceTy   : ProjectedInterfaceTy labelTy endpoint interfaceTy)
              -> Type
  where
    MkInterface : (name            : VLNV)
               -> (endian          : Maybe Endian)
               -> (mustBeConnected : Bool)
               -> (doc             : DocString)
               -> (ports           : PortGroup annot labelTy endpoint endian (portTys ++ flatten chans) pportTys)
               -> Interface annot labelTy endpoint kind endian (MkInterfaceTy  vlnv  i cStyle mp mc portTys chans doc')
                                                               (MkPInterfaceTy vlnv    cStyle pportTys)

portGroup : Interface annot labelTy endpoint kind endian iType iPType
     -> PortGroup annot labelTy endpoint endian (fullPortGroupTy iType) (projectedPortGroup iPType)
portGroup (MkInterface name endian mustBeConnected doc ports) = ports


{- [ NOTE ]

  We source the projected port types from the projected interface.

-}

||| Project an interface based on a given interface kind.
projectByKind : {endpoint : Endpoint}
             -> (kind : InterfaceKind isMonitor endpoint)
             -> (interfaceTy : InterfaceTy annot labelTy)
             -> ProjectedInterfaceTy labelTy endpoint interfaceTy
projectByKind kind interfaceTy {endpoint} = projectInterface endpoint interfaceTy

||| A collection of interfaces.
data Interfaces : (annot : Type)
               -> (kinds         : InterfaceKinds ks)
               -> (interfaceTys  : InterfaceTys annot labelTys)
               -> Type where
  Nil  : Interfaces annot Nil Nil
  (::) : Interface annot labelTy endpoint kind endian interfaceTy (projectByKind kind interfaceTy)
      -> Interfaces annot kinds interfaceTys
      -> Interfaces annot (kind::kinds) (interfaceTy::interfaceTys)


namespace Typed

  ||| Interface definition that calculates the projected interface
  ||| using a given interface type definition, and the projection
  ||| kind.
  Interface : (annot       : Type)
           -> (labelTy       : Type)
           -> (endpoint    : Endpoint)
           -> (kind        : InterfaceKind isMonitor endpoint)
           -> (endian      : Maybe Endian)
           -> (interfaceTy : InterfaceTy annot labelTy)
           -> Type
  Interface annot labelTy endpoint kind endian interfaceTy =
    Interface.Interface annot labelTy endpoint kind endian interfaceTy (projectByKind kind interfaceTy)

  namespace Dictated

    ||| Interface definition that calculates the projected interface
    ||| using a given interface type definition, and the projection
    ||| kind.
    Interface : (annot : Type)
             -> (labelTy : Type)
             -> (kind        : InterfaceKind isMonitor endpoint)
             -> (endian      : Endian)
             -> (interfaceTy : InterfaceTy annot labelTy)
             -> Type
    Interface annot labelTy {endpoint} kind endian interfaceTy =
      Interface.Interface annot labelTy endpoint kind (Just endian) interfaceTy (projectByKind kind interfaceTy)


    PortGroup : (annot  : Type)
             -> (labelTy  : Type)
             -> (type   : InterfaceTy annot labelTy)
             -> (kind   : InterfaceKind isMonitor endpoint)
             -> (endian : Endian)
             -> Type
    PortGroup annot labelTy {endpoint} type kind endian =
      PortGroup.PortGroup annot
                          labelTy
                          endpoint
                          (Just endian)
                          (portGroupTy type ++ flatten (channels type))
                          (projectedPortGroup (projectInterface endpoint type))


  namespace Free
    ||| Interface definition that calculates the projected interface
    ||| using a given interface type definition, and the projection
    ||| kind.
    Interface : (annot       : Type)
             -> (labelTy       : Type)
             -> (kind        : InterfaceKind isMonitor endpoint)
             -> (interfaceTy : InterfaceTy annot labelTy)
             -> Type
    Interface annot labelTy {endpoint} kind interfaceTy =
      Interface.Interface annot labelTy endpoint kind Nothing interfaceTy (projectByKind kind interfaceTy)

    PortGroup : (annot   : Type)
             -> (labelTy   : Type)
             -> (type    : InterfaceTy annot labelTy)
             -> (kind    : InterfaceKind isMonitor endpoint)
             -> Type
    PortGroup annot labelTy {endpoint} type kind =
      PortGroup.PortGroup annot
                          labelTy
                          endpoint
                          Nothing
                          (portGroupTy type ++ flatten (channels type))
                          (projectedPortGroup (projectInterface endpoint type))

  newInterface : (interfaceTy     : InterfaceTy annot labelTy)
              -> (kind            : InterfaceKind isMonitor endpoint)
              -> (name            : VLNV)
              -> (endian          : Maybe Endian)
              -> (mustBeConnected : Bool)
              -> (doc             : DocString)
              -> (ports           : PortGroup annot labelTy endpoint endian
                                       (portGroupTy interfaceTy ++ flatten (channels interfaceTy))
                                       (projectedPortGroup (projectInterface endpoint interfaceTy)))
              -> Interface annot labelTy endpoint kind endian interfaceTy (projectInterface endpoint interfaceTy)
  newInterface type k n e mustConn doc ps with (type)
    newInterface type k n e mustConn doc ps | (MkInterfaceTy name info cstyle maxProducers maxConsumers portGroupTy channels x) =
      MkInterface n e mustConn doc ps

  namespace NoDoc
    newInterface : (interfaceTy     : InterfaceTy annot labelTy)
                -> (kind            : InterfaceKind isMonitor endpoint)
                -> (name            : VLNV)
                -> (endian          : Maybe Endian)
                -> (mustBeConnected : Bool)
                -> (ports           : PortGroup annot labelTy endpoint endian
                                          (portGroupTy interfaceTy ++ flatten (channels interfaceTy))
                                          (projectedPortGroup (projectInterface endpoint interfaceTy)))
                -> Interface annot labelTy endpoint kind endian interfaceTy (projectInterface endpoint interfaceTy)
    newInterface type kind name endian mustConn ps with (type)
      newInterface type kind name endian mustConn ps | (MkInterfaceTy x info cstyle maxProducers maxConsumers portGroupTy channels doc) =
        MkInterface name endian mustConn Empty ps

-- --------------------------------------------------------------------- [ EOF ]
