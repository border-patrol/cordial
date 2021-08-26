module Cordial.Model.Interface.Ports

import Data.Vect
import Data.DList
import Commons.Data.Ranged

import Text.Markup.Edda

import Cordial.Model.Common
import Cordial.Model.Specification
import Cordial.Model.Projection

import Cordial.Model.Interface.Kinds


%default total
%access public export

--@TODO make width better.

||| Physical manifestation of a port on an IP Core interface.
|||
||| @annot Some annotation.
||| @labelTy Universe that logical names arise from.
||| @endpoint Are we producing/consuming information.
||| @pportTy  The originating projected port type that constrains the value level values.
|||
data Port : (annot    : Type)
         -> (labelTy    : Type)
         -> (portTy   : PortTy annot labelTy)
         -> (pportTy  : ProjectedPortTy labelTy endpoint portTy)
         -> (endpoint : Endpoint)
         -> (endian   : Maybe Endian)
         -> Type
  where

    General : (info        : annot)
           -> (doc         : DocString)
           -> (origin      : Origin)
           -> (sensitivity : Sensitivity)
           -> (label       : Name nKind labelTy)
           -> (width       : PortWidth wty dwidth)
           -> (direction   : Direction endpoint flow)
           -> (dendian     : DataEndian endian)
           -> Port annot labelTy
                   (PortDesc  info' wty label General flow      dwidth sensitivity opt      origin vorigin doc')
                   (PPortDesc       wty label General direction dwidth sensitivity required origin vorigin)
                   endpoint endian

    Information : (info        : annot)
               -> (doc         : DocString)
               -> (origin      : Origin)
               -> (sensitivity : Sensitivity)
               -> (label       : Name nKind labelTy)
               -> (width       : PortWidth wty dwidth)
               -> (direction   : Direction endpoint flow)
               -> (dendian     : DataEndian endian)
               -> Port annot labelTy
                       (PortDesc  info' wty label Information flow      dwidth sensitivity opt      origin vorigin doc')
                       (PPortDesc       wty label Information direction dwidth sensitivity required origin vorigin)
                       endpoint endian

    Clock : (info        : annot)
         -> (doc         : DocString)
         -> (origin      : Origin)
         -> (width       : PortWidth WIRE dwidth)
         -> (label       : Name nKind labelTy)
         -> (direction   : Direction endpoint flow)
         -> (sensitivity : Sensitivity)
         -> (clockInfo   : ClockInfo (Clock mce md mtc) direction)
         -> Port annot labelTy
                 (PortDesc  info' WIRE label (Clock mce md mtc) flow      dwidth sensitivity opt      origin vorigin doc')
                 (PPortDesc       WIRE label (Clock mce md mtc) direction dwidth sensitivity required origin vorigin)
                 endpoint endian

    Address : (info        : annot)
           -> (doc         : DocString)
           -> (origin      : Origin)
           -> (sensitivity : Sensitivity)
           -> (label       : Name nKind labelTy)
           -> (width       : PortWidth ARRAY dwidth)
           -> (direction : Direction endpoint flow)
           -> (dendian : DataEndian endian)
           -> Port annot labelTy
                   (PortDesc  info' ARRAY  label AddressWire flow      dwidth sensitivity opt      origin vorigin doc')
                   (PPortDesc        ARRAY label AddressWire direction dwidth sensitivity required origin vorigin)
                   endpoint endian

    Data : (info        : annot)
        -> (doc         : DocString)
        -> (origin      : Origin)
        -> (sensitivity : Sensitivity)
        -> (label       : Name nKind labelTy)
        -> (width       : PortWidth ARRAY dwidth)
        -> (direction   : Direction endpoint flow)
        -> (dendian     : DataEndian endian)
        -> Port annot labelTy
                (PortDesc  info' ARRAY label DataWire flow      dwidth sensitivity opt      origin vorigin doc')
                (PPortDesc       ARRAY label DataWire direction dwidth sensitivity required origin vorigin)
                endpoint endian

    Reset : (info        : annot)
         -> (doc         : DocString)
         -> (origin      : Origin)
         -> (size        : PortWidth WIRE dwidth)
         -> (label       : Name nKind labelTy)
         -> (direction   : Direction endpoint flow)
         -> (sensitivity : Sensitivity)
         -> Port annot labelTy
                  (PortDesc  info' WIRE label Reset flow      dwidth sensitivity opt      origin vorigin doc')
                  (PPortDesc       WIRE label Reset direction dwidth sensitivity required origin vorigin)
                  endpoint endian

    Interrupt : (info        : annot)
             -> (doc         : DocString)
             -> (origin      : Origin)
             -> (size        : PortWidth WIRE dwidth)
             -> (label       : Name nKind labelTy)
             -> (direction   : Direction endpoint flow)
             -> (sensitivity : Sensitivity)
             -> Port annot labelTy
                      (PortDesc  info' WIRE label Interrupt flow      dwidth sensitivity opt      origin vorigin doc')
                      (PPortDesc       WIRE label Interrupt direction dwidth sensitivity required origin vorigin)
                      endpoint endian

    Control : (info        : annot)
           -> (doc         : DocString)
           -> (origin      : Origin)
           -> (size        : PortWidth WIRE dwidth)
           -> (label       : Name nKind labelTy)
           -> (direction   : Direction endpoint flow)
           -> (sensitivity : Sensitivity)
           -> Port annot labelTy
                    (PortDesc info' WIRE label Control flow      dwidth sensitivity opt      origin vorigin doc')
                    (PPortDesc      WIRE label Control direction dwidth sensitivity required origin vorigin)
                    endpoint endian

namespace Calculated
  Port : (annot : Type)
      -> (labelTy : Type)
      -> (endpoint : Endpoint)
      -> (endian : Maybe Endian)
      -> (portType : PortTy annot labelTy)
      -> Type
  Port x labelTy endpoint endian portType =
    Ports.Port x labelTy portType (projectPort endpoint portType) endpoint endian

data OptionalPort : (p : Port annot labelTy type projectedType endpoint endian) -> Type where
  PortIsOptional : (prfType : OptionalPortType endpoint type)
                -> (prfProjection : OptionalProjectedPort type endpoint projectedType)
                -> (port : Port annot labelTy type projectedType endpoint endian)
                -> OptionalPort port

data SystemPort : (p : Port annot labelTy type projectedType endpoint endian) -> Type where
  PortIsSystem : (port : Port annot labelTy type projectedType endpoint endian)
              -> (prfProjection : SystemProjectedPort type projectType)
              -> SystemPort port

data IPPort : (p : Port annot labelTy type projectedType endpoint endian) -> Type where
  PortIsIP : (port : Port annot labelTy type projectedType endpoint endian)
          -> (prfProjection : IPProjectedPort type projectedType)
          -> IPPort port

isSystemPort_rhs_rhs_2 : (contra : SystemProjectedPort type projectedType -> Void) -> SystemPort p -> Void
isSystemPort_rhs_rhs_2 contra (PortIsSystem p prfProjection) = contra (ProjectedPortIsSystem ?isSystemPort_rhs_rhs_2_rhs_2)

isSystemPort : (p : Port annot labelTy type projectedType endpoint endian)
            -> Dec (SystemPort p)
isSystemPort p {projectedType} with (isProjectedPortSystem projectedType)
  isSystemPort p {projectedType = projectedType} | (Yes prf) = Yes (PortIsSystem p prf)
  isSystemPort p {projectedType = projectedType} | (No contra) = No (isSystemPort_rhs_rhs_2 contra)



-- --------------------------------------------------------------------- [ EOF ]
