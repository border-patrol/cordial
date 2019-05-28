-- ---------------------------------------------------------- [ Projection.idr ]
-- Module    : Projection.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| How to project Interface Descriptions to local descriptions.
module Cordial.Model.Projection

import Data.Vect
import Data.DList

import Text.Markup.Edda

import public Cordial.Model.Common
import        Cordial.Model.Specification

%hide DList.map

%default total
%access public export

||| Projected port models abstractly an interfaces structure.
|||
||| A projected port is similar to an abstract port type with two major differences.
|||
||| 1. Flows reconstituted as directions based on the endpoint; and
||| 2. Use of the port (required or optional) translated from abstract port.
data ProjectedPortTy : (labelTy  : Type)
                    -> (endpoint : Endpoint)
                    -> (type   : PortTy annot labelTy)
                    -> Type
  where
    PPortDesc : (kind   : PortShape)
             -> (label  : Name nKind labelTy)
             -> (wireTy : WireTy)
             -> (dir    : Direction endpoint flow)
             -> (pwidth : PortWidthDesc kind)

             -> (sens   : Sensitivity)

             -> (required : Necessary endpoint req)

             -> (origin : Origin)

             -> (vorigin  : ValueOrigin width)

             -> ProjectedPortTy labelTy
                                endpoint
                                (PortDesc i kind label wireTy flow width sens req origin vorigin doc)

necessary : ProjectedPortTy labelTy endpoint type
         -> Necessary (calcOptTy endpoint (required type)) endpoint (required type) (calcOptKind endpoint (required type))
necessary (PPortDesc kind label wireTy dir pwidth sens required origin vorigin) = required

origin : (o : Origin)
      -> ProjectedPortTy l e (PortDesc i kind label wireTy flow width sens req origin vorigin doc)
      -> ProjectedPortTy l e (PortDesc i kind label wireTy flow width sens req o      vorigin doc)
origin o (PPortDesc k l w d p s r _ vo) = (PPortDesc k l w d p s r o vo)

data OptionalProjectedPort : (type : PortTy annot labelTy)
                          -> (endpoint : Endpoint)
                          -> (projectedType : ProjectedPortTy labelTy endpoint type)
                          -> Type
    where
      ProjectedPortIsOptional : (prf : OptionalPortType endpoint type)
                             -> OptionalProjectedPort type endpoint projectedType

data SystemProjectedPort : (type : PortTy annot labelTy)
                        -> (projectedType : ProjectedPortTy labelTy endpoint type)
                        -> Type
    where
      ProjectedPortIsSystem : (prf : SystemPortType type)
                           -> SystemProjectedPort type projectedType

data IPProjectedPort : (type : PortTy annot labelTy)
                    -> (projectedType : ProjectedPortTy labelTy endpoint type)
                    -> Type
    where
      ProjectedPortIsIP : (prf : IPPortType type)
                       -> IPProjectedPort type projectedType

projectedPortIsIP : (contra : SystemPortType type -> Void) -> SystemProjectedPort type projectedType -> Void
projectedPortIsIP contra (ProjectedPortIsSystem prf) = contra prf

projectedPortIsSystem : (contra : IPPortType type -> Void) -> IPProjectedPort type projectedType -> Void
projectedPortIsSystem contra (ProjectedPortIsIP prf) = contra prf

isProjectedPortIP : (projectedType : ProjectedPortTy labelTy endpoint type)
                 -> Dec (IPProjectedPort type projectedType)
isProjectedPortIP projectedType {type} with (isPortTypeIP type)
  isProjectedPortIP projectedType {type = type} | (Yes prf) = Yes (ProjectedPortIsIP prf)
  isProjectedPortIP projectedType {type = type} | (No contra) = No (projectedPortIsSystem contra)

isProjectedPortSystem : (projectedType : ProjectedPortTy labelTy endpoint type)
                     -> Dec (SystemProjectedPort type projectedType)
isProjectedPortSystem projectedType {type} with (isPortTypeSystem type)
  isProjectedPortSystem projectedType {type = type} | (Yes prf) = Yes (ProjectedPortIsSystem prf)
  isProjectedPortSystem projectedType {type = type} | (No contra) = No (projectedPortIsIP contra)


||| Projected port group is a list of projected ports in which we
||| collect at the type level the abstract ports indexing the
||| projected port types.
ProjectedPortGroupTy : (labelTy : Type)
                    -> (endpoint : Endpoint)
                    -> List (PortTy annot labelTy)
                    -> Type
ProjectedPortGroupTy labelTy endpoint =
  DList (PortTy annot labelTy) (ProjectedPortTy labelTy endpoint)


mapDList : (tyF  : aTy -> bTy)
        -> (valF : {a : aTy} -> {b : bTy} -> eTy a -> fTy b)
        -> DList.DList aTy eTy as
        -> DList.DList bTy fTy (map tyF as)
mapDList tyF valF []      = []
mapDList tyF valF (x::xs) = valF x :: Projection.mapDList tyF valF xs

setOrigin : (o : Origin)
       -> ProjectedPortGroupTy labelTy endpoint ps
       -> ProjectedPortGroupTy labelTy endpoint (map (record {origin = o}) ps)
setOrigin o pps with (pps)
  setOrigin o pps | [] = []
  setOrigin o pps | (elem :: rest) with (elem)
    setOrigin o pps | (elem :: rest) | (PPortDesc kind label wireTy dir pwidth sens required origin vorigin) =
     PPortDesc kind label wireTy dir pwidth sens required o vorigin :: setOrigin o rest

||| A projected interface is similar to an abstract interface but
||| containing list of projected ports.
|||
data ProjectedInterfaceTy : (labelTy     : Type)
                         -> (endpoint    : Endpoint)
                         -> (interfaceTy : InterfaceTy annot labelTy)
                         -> Type
  where
    MkPInterfaceTy : (vlnv : VLNV)
                  -> (commStyle : CommStyle)
                  -> (portgroup : ProjectedPortGroupTy labelTy endpoint (portTys ++ flatten chans))
                  -> ProjectedInterfaceTy labelTy endpoint (MkInterfaceTy vlnv i commStyle mc mp portTys chans doc)

projectedPortGroup : ProjectedInterfaceTy labelTy endpoint interfaceTy
                   -> ProjectedPortGroupTy labelTy endpoint (portGroupTy interfaceTy ++ flatten (channels interfaceTy))
projectedPortGroup (MkPInterfaceTy vlnv cStyle portgroup) = portgroup


||| A collection of projected interfaces.
data ProjectedInterfaceTys : (hs : List Type)
                          -> (interfaceTys : InterfaceTys annot hs)
                          -> (es           : List Endpoint)
                          -> Type
  where
    Nil : ProjectedInterfaceTys Nil Nil Nil
    (::) : {i : InterfaceTy annot labelTy}
        -> ProjectedInterfaceTy labelTy e i
        -> ProjectedInterfaceTys hs is es
        -> ProjectedInterfaceTys (labelTy::hs) (i :: is) (e::es)

data ProjectTypes : (endpoint : Endpoint)
                 -> (flow     : Flow)
                 -> (dty      : DirectionTy)
                 -> (opt      : OptionalTy)
                 -> (oty      : OptTy)
                 -> Type where
  Witness : (necessary : Necessary (calcOptTy endpoint opt) endpoint opt (calcOptKind endpoint opt))
         -> (direction : Direction (calcDirTy endpoint flow) endpoint flow (calcDirKind endpoint flow))
         -> ProjectTypes endpoint flow (calcDirTy endpoint flow) opt (calcOptTy endpoint opt)

projectTypes : (endpoint : Endpoint)
            -> (flow     : Flow)
            -> (opt      : OptionalTy)
            -> ProjectTypes endpoint flow (calcDirTy endpoint flow) opt (calcOptTy endpoint opt)
projectTypes endpoint flow opt = Witness (calcNecessary endpoint opt) (calcDirection endpoint flow)


||| Project an abstract port description according to the presented endpoint.
|||
||| @endpoint The 'direction' to project in.
||| @portTy   The abstract port to project.
projectPort : (endpoint : Endpoint)
           -> (portTy   : PortTy annot labelTy)
           -> ProjectedPortTy labelTy endpoint portTy
projectPort e p with (p)
  projectPort e p | (PortDesc info kind label wkind flow width sens required origin valueOrigin doc) with (projectTypes e flow required)
    projectPort e p | (PortDesc info kind label wkind flow width sens required origin valueOrigin doc) | (Witness necessary direction) =
      PPortDesc kind label wkind direction width sens necessary origin valueOrigin

||| Project an abstract interface description according to the presented endpoint.
|||
||| @endpoint    The 'direction' to project in.
||| @interfaceTy The abstract interface to project.
projectInterface : (endpoint    : Endpoint)
                -> (interfaceTy : InterfaceTy annot labelTy)
                -> ProjectedInterfaceTy labelTy endpoint interfaceTy
projectInterface endpoint (MkInterfaceTy vlnv info commStyle maxConsumers maxProducers ports chans doc) =
    MkPInterfaceTy vlnv commStyle (projectPorts ports ++ projectPorts (flatten chans))
  where
    projectPorts : (ps : List (PortTy annot labelTy))
                -> DList (PortTy annot labelTy) (ProjectedPortTy labelTy endpoint) ps
    projectPorts [] = []
    projectPorts (x :: xs) = projectPort endpoint x :: projectPorts xs

-- --------------------------------------------------------------------- [ EOF ]
