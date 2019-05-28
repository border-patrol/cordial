-- ----------------------------------------------------------- [ Component.idr ]
-- Module    : Component.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| Definition of an IP Core.
|||
||| We call IP Cores components because...
module Cordial.Model.Component

import Data.DList

import Text.Markup.Edda

import public Cordial.Model.Common
import        Cordial.Model.Specification
import public Cordial.Model.Projection
import public Cordial.Model.Interface

%default total
%access public export

data TrustKind = Trusted | UnTrusted

||| Representation of an IP Core as a list of interfaces.
|||
||| @trusted Do we trust the underlying IP Core.
||| @kinds   Collect the Kinds of interface the IP Core has.
||| @interfaceTys Collect the top level abstract description that each interface models.
data Component : (annot : Type)
              -> (trusted       : TrustKind)
              -> (kinds         : InterfaceKinds ks)
              -> (interfaceTys  : InterfaceTys annot tts)
              -> Type
  where
    MkComponent : (info : annot)
               -> (name : VLNV)
               -> (doc : DocString)
               -> (t : TrustKind)
               -> (interfaces : Interfaces annot kinds itys)
               -> Component annot t kinds itys

||| Add an interface to an IP Core.
|||
||| We make explicit the interface kind, type, and structure.
addInterface : (c    : Component annot t ks types)
            -> (kind : InterfaceKind b e)
            -> (type : InterfaceTy annot labelTy)
            -> (i    : Interface annot labelTy e kind endian type (projectByKind kind type))
            -> Component annot t (kind::ks) (type::types)
addInterface (MkComponent info name doc t is) kind type i = MkComponent info name doc t (i :: is)

-- --------------------------------------------------------------------- [ EOF ]
