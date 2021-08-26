module Cordial.Model.Interface.PortGroup

import Data.Vect
import Data.DList

import Commons.Data.Ranged

import Text.Markup.Edda

import Cordial.Model.Common
import Cordial.Model.Specification
import Cordial.Model.Projection

import Cordial.Model.Interface.Kinds
import Cordial.Model.Interface.Ports

%default total
%access public export

{- [ NOTE ]

We take note, at the type level, if the port is required or not. We
use this information with `PortGroup` below to describe thinnings.

With Port notice how we constrain the value level values using type
level values. This is core principle behind how we type check our
ports/interfaces against an abstract definition. We first project the
definition based on the kind of interface, and use that projection in
the type to source values.

-}


||| A collection of ports that respects the projected port group.
|||
||| Universe that logical names arise from.
||| Are we producing/consuming information.
||| The originating projected port type that constrains the value level values.
|||
data PortGroup : (annot    : Type)
              -> (labelTy  : Type)
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
    Add  : {type : PortTy annot labelTy}
        -> {projectedType : ProjectedPortTy labelTy endpoint type}
        -> (port : Port annot labelTy type projectedType endpoint endian)

        -> (rest : PortGroup annot labelTy endpoint endian ps pps)
        -> PortGroup annot labelTy endpoint endian (type          :: ps)
                                                   (projectedType :: pps)

    ||| Skip an optional port from the projected port list.
    Skip : (rest : PortGroup annot labelTy endpoint endian ps pps)
        -> (prf  : OptionalProjectedPort type endpoint projectedType)
        -> PortGroup annot labelTy endpoint endian (type :: ps) (projectedType :: pps)

infixr 5 <::>, <::~>

(<::>) : {type : PortTy annot labelTy}
      -> {projectedType : ProjectedPortTy labelTy endpoint type}
      -> (port : Port annot labelTy type projectedType endpoint endian)
      -> (rest : PortGroup annot labelTy endpoint endian ps pps)
      -> PortGroup annot labelTy endpoint endian (type::ps) (projectedType::pps)
(<::>) port rest = Add port rest

(<::~>) : (port : Port annot labelTy type projectedType endpoint endian)
       -> (rest : PortGroup annot labelTy endpoint endian ps pps)
       -> {auto prf : OptionalProjectedPort typeOfSkipped endpoint projectedTypeOfSkipped}
       -> PortGroup annot labelTy endpoint endian
                    (type::typeOfSkipped::ps)
                    (projectedType::projectedTypeOfSkipped::pps)
(<::~>) port rest {prf} = Add port (Skip rest prf)


-- --------------------------------------------------------------------- [ EOF ]
