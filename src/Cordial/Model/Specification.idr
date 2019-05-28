-- --------------------------------------------------------- [ Description.idr ]
-- Module    : Description.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| Data types for modelling abstract descriptions of interfaces.
module Cordial.Model.Specification

import        Data.Vect
import        Data.DList
import public Cordial.Model.Common

%default total
%access public export

||| Individual port in an interface.
|||
record PortTy annot (labelTy : Type) where
  constructor PortDesc
  info : annot
  kind  : PortShape
  label : Name nKind labelTy
  wkind : WireTy
  flow  : Flow
  width : PortWidthDesc kind

  sens  : Sensitivity

  required : OptionalTy
  origin   : Origin

  valueOrigin  : ValueOrigin width
  doc          : DocString

data OptionalPortType : (endpoint : Endpoint) -> (type : PortTy annot labelTy) -> Type where
  IsOptionalPortType : (prf : OptionalKind endpoint optTy OPT)
                    -> OptionalPortType endpoint (PortDesc i k l ty f w s optTy o vo doc)

data SystemPortType : (type : PortTy annot labelTy) -> Type where
   IsSystemPortType : (name : String) -> SystemPortType (PortDesc i k l ty f w s optTy (SYSTEM name) vo doc)

data IPPortType : (type : PortTy annot labelTy) -> Type where
   IsIPPortType : IPPortType (PortDesc i k l ty f w s optTy IP vo doc)

portIsSystem : IPPortType (PortDesc i k l wk f w s r (SYSTEM x) v d)
            -> Void
portIsSystem IsIPPortType impossible

portIsIP : SystemPortType (PortDesc i k l wk f w s r IP v d)
        -> Void
portIsIP (IsSystemPortType _) impossible

isPortTypeSystem : (type : PortTy annot labelTy)
                -> Dec (SystemPortType type)
isPortTypeSystem (PortDesc info kind label wkind flow width sens required (SYSTEM x) valueOrigin doc) = Yes (IsSystemPortType x)
isPortTypeSystem (PortDesc info kind label wkind flow width sens required IP valueOrigin doc) = No portIsIP

isPortTypeIP : (type : PortTy annot labelTy)
           -> Dec (IPPortType type)
isPortTypeIP (PortDesc info kind label wkind flow width sens required (SYSTEM x) valueOrigin doc) = No portIsSystem
isPortTypeIP (PortDesc info kind label wkind flow width sens required IP valueOrigin doc) = Yes IsIPPortType

||| Collection of Ports
PortGroupTy : (annot : Type) -> (labelTy : Type) -> Type
PortGroupTy annot labelTy = List (PortTy annot labelTy)

record Channel (annot : Type) (labelTy : Type) where
  constructor MkChan
  name : String
  info : annot
  ports : PortGroupTy annot labelTy

flatten : List (Channel annot labelTy) -> PortGroupTy annot labelTy
flatten Nil     = Nil
flatten (c::cs) = ports c ++ flatten cs

||| An interface is a list of ports with a given number of producers
||| and consumers, and a communication style.
|||
record InterfaceTy (annot : Type) (labelTy : Type) where
   constructor MkInterfaceTy
   name         : VLNV
   info         : annot
   cstyle       : CommStyle
   maxProducers : Whole
   maxConsumers : Whole
   portGroupTy  : PortGroupTy annot labelTy
   channels     : List (Channel annot labelTy)
   doc          : DocString

fullPortGroupTy : InterfaceTy annot labelTy -> PortGroupTy annot labelTy
fullPortGroupTy iface = (portGroupTy iface) ++ (flatten $ channels iface)

||| Collection of interfaces
data InterfaceTys : (annot : Type) -> (labelTys : List Type)-> Type where
  Nil  : InterfaceTys  annot Nil
  (::) : InterfaceTy   annot labelTy
      -> InterfaceTys  annot hs
      -> InterfaceTys  annot (labelTy::hs)

data IsBroadcast : InterfaceTy annot labelTy -> Type where
  YesIsBroadcast : IsBroadcast (MkInterfaceTy n i Broadcast p c ps cs doc)
-- --------------------------------------------------------------------- [ EOF ]
