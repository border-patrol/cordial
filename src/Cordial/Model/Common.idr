-- ---------------------------------------------------------------- [ Core.idr ]
-- Module    : Core.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| Core Data Types used in Cordial
module Cordial.Model.Common

import Commons.Data.Ranged
import Data.Vect
import Text.Markup.Edda

import public Cordial.Model.Common.Essential
import public Cordial.Model.Common.VLNV
import public Cordial.Model.Common.Widths
import public Cordial.Model.Common.Hacks
import public Cordial.Model.Common.Whole
import public Cordial.Model.Common.WireTy
import public Cordial.Model.Common.Direction
import public Cordial.Model.Common.Necessary
import public Cordial.Model.Common.Label
import public Cordial.Model.Common.Name

%default total
%access public export

namespace ClockInfo

  data ClockInfo : (wty : WireTy) -> (dir : Direction ty endpoint flow prf) -> Type where
    MkCOut : (mce   : Maybe ClockEdge)
          -> (md    : Maybe Delay)
          -> (mtc   : Maybe (RangedNat 0 100))
          -> (phase : RangedNat 0 360)
          -> (freq  : Nat)
          -> ClockInfo (Clock mce md mtc) OUT
    MkCIn : (mce   : Maybe ClockEdge)
         -> (md    : Maybe Delay)
         -> (mtc   : Maybe (RangedNat 0 100))
         -> (phase : Maybe (RangedNat 0 360))
         -> (freq  : Maybe Nat)
         -> ClockInfo (Clock mce md mtc) IN

namespace DataEndian

  data DataEndian : Maybe Endian -> Type where
    Dictated : (endian : Endian) -> DataEndian (Just endian)
    Free     : (endian : Endian) -> DataEndian Nothing


namespace Extension
  data ExtensionTy = DESCRIPTION
                   | PORTDESC WireTy
                   | PORT WireTy
                   | COMPONENT
                   | INTERFACE
                   | DESIGN
                   | CONNECTION ConnectionTy

  ExtensionKind : Type
  ExtensionKind = (ExtensionTy -> Type)

  data VendorExt : (ty : ExtensionTy) -> Type where
    Ext : {kind : ExtensionTy -> Type} -> (value : kind ty) -> VendorExt ty
    Empty : VendorExt ty

namespace DocString

  data IsRight : Either a b -> Type where
    ItIsRight : IsRight (Right value)

  Uninhabited (IsRight (Left l)) where
    uninhabited ItIsRight impossible

  data DocString : Type where
    Empty : DocString
    Doc   : (src : Edda SNIPPET)
         -> DocString

  newDocString : (src : String)
              -> (p   : String -> Either String (Edda SNIPPET))
              -> DocString
  newDocString src p with (p src)
    newDocString src p | (Left l) = Empty
    newDocString src p | (Right r) = Doc r

  toString : (Edda SNIPPET -> String) -> DocString -> String
  toString _ Empty = ""
  toString p (Doc src) = p src


namespace Driver
  data Driver = Any | Clock | SingleShot

namespace Value
  data ValueOrigin : PortWidthDesc shape -> Type where
    DefaultValue   : Vect (toNat w) Value -> ValueOrigin w
    Zeroed         : ValueOrigin w
    RequiresDriver : Driver -> ValueOrigin w
    NoValue        : ValueOrigin w

-- ----------------------------------------- [ High-Level Protocol Information ]

namespace Protocol

  record ProtocolInfo where
    constructor MkPInfo
    protocolType : Maybe String
    payloadName  : String
    payloadType  : String

-- --------------------------------------------------------------------- [ EOF ]
