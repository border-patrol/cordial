module Cordial.EDSL.Specification.API

import Data.Vect
import Data.List.Quantifiers
import Data.Ranged

import Text.Markup.Edda

import Language.EDSL.SingleStateVar

import Cordial.Model.Specification

import Cordial.EDSL.Specification.Lang

%default total
%access public export


namespace Signals

  defSig : (label  : Var)
        -> (kind   : PortShape)
        -> (wirety : WireTy)
        -> (width  : PortWidthDesc kind)

        -> (idx : InContext (CanUseVar labelTy label) old)

        -> LangM m () (LangIDL labelTy) (TyExpr DECL) old (const $ update Consume old idx)

  defSig var k' k w idx =
    signal var k' k PC w High IsRequired IP NoValue Empty idx

  replicate : (n : Nat)
           -> LangM m () (LangIDL labelTy) (TyExpr DECL) old newK
           -> LangM m () (LangIDL labelTy) (TyExpr DECL) old newK
  replicate n (Expr (DeclareSignal label kind wirety flow width sense required origin vorigin doc prf)) =
    Expr (Replicate n label kind wirety flow width sense required origin vorigin doc prf)
  replicate n (Expr (Replicate k var kind wirety flow width sense required origin vorigin doc prf)) =
    Expr (Replicate n var kind wirety flow width sense required origin vorigin doc prf)

  namespace Generic

    general : (label : Var)
           -> (kind : PortShape)
           -> {auto idx : InContext (CanUseVar labelTy label) old}
           -> LangM m () (LangIDL labelTy) (TyExpr DECL) old (const $ update Consume old idx)
    general var kind {idx} = defSig var kind General UserDefined idx

    clock : (label  : Var)
         -> (edge   : Maybe ClockEdge)
         -> (delay  : Maybe Delay)
         -> (tcons  : Maybe (RangedNat 0 100))

         -> {auto idx : InContext (CanUseVar labelTy label) old}

         -> LangM m () (LangIDL labelTy) (TyExpr DECL) old (const $ update Consume old idx)
    clock var e d t {idx} =
      defSig var WIRE (Clock e d t) One idx


    control : (label : Var)
           -> {auto idx : InContext (CanUseVar labelTy label) old}
           -> LangM m () (LangIDL labelTy) (TyExpr DECL) old (const $ update Consume old idx)
    control var {idx} = defSig var WIRE Control One idx

    interrupt : (label    : Var)
             -> {auto idx : InContext (CanUseVar labelTy label) old}
             -> LangM m () (LangIDL labelTy) (TyExpr DECL) old (const $ update Consume old idx)
    interrupt var {idx} = defSig var WIRE Interrupt One idx


    reset : (label : Var)
         -> {auto idx : InContext (CanUseVar labelTy label) old}
         -> LangM m () (LangIDL labelTy) (TyExpr DECL) old (const $ update Consume old idx)
    reset var {idx} = defSig var WIRE Reset One  idx


    info : (label : Var)
        -> (width : PortWidthDesc ARRAY)
        -> {auto idx : InContext (CanUseVar labelTy label) old}
        -> LangM m () (LangIDL labelTy) (TyExpr DECL) old (const $ update Consume old idx)
    info var width {idx} = defSig var ARRAY Information width idx

    bus : (label : Var)
       -> (width : PortWidthDesc ARRAY)
       -> {auto idx : InContext (CanUseVar labelTy label) old}
       -> LangM m () (LangIDL labelTy) (TyExpr DECL) old (const $ update Consume old idx)
    bus var width {idx} = defSig var ARRAY DataWire width idx

    address : (label : Var)
           -> (width  : PortWidthDesc ARRAY)
           -> {auto idx : InContext (CanUseVar labelTy label) old}
           -> LangM m () (LangIDL labelTy) (TyExpr DECL) old (const $ update Consume old idx)
    address var width {idx} = defSig var ARRAY AddressWire width idx

  namespace Unrestricted

    info : (label  : Var)
        -> {auto idx : InContext (CanUseVar labelTy label) old}
        -> LangM m () (LangIDL labelTy) (TyExpr DECL) old (const $ update Consume old idx)
    info var {idx} = Generic.info var UserDefined {idx=idx}

    bus : (label : Var)
       -> {auto idx : InContext (CanUseVar labelTy label) old}
       -> LangM m () (LangIDL labelTy) (TyExpr DECL) old (const $ update Consume old idx)
    bus var {idx} = Generic.bus var UserDefined {idx=idx}

    address : (label : Var)
           -> {auto idx : InContext (CanUseVar labelTy label) old}
           -> LangM m () (LangIDL labelTy) (TyExpr DECL) old (const $ update Consume old idx)
    address var {idx} = Generic.address var UserDefined {idx=idx}


namespace Accessor

  setDoc : (d   : String -> Either String (Edda SNIPPET))
        -> (src : String)
        -> LangM m () (LangIDL labelTy) (TyExpr DECL) old newK
        -> LangM m () (LangIDL labelTy) (TyExpr DECL) old newK
  setDoc d src (Expr (DeclareSignal label kind wirety flow width sense required origin defaultValue doc idx)) =
    Expr (DeclareSignal label kind wirety flow width sense required origin defaultValue (newDocString src d) idx)
  setDoc d src (Expr (Replicate n label kind wirety flow width sense required origin defaultValue doc idx)) = Expr (Replicate n label kind wirety flow width sense required origin defaultValue (newDocString src d) idx)

namespace Modifier

  system : String
        -> LangM m () (LangIDL labelTy) (TyExpr DECL) old newK
        -> LangM m () (LangIDL labelTy) (TyExpr DECL) old newK
  system n (Expr (DeclareSignal label kind wirety flow width sense required origin defaultValue doc idx)) =
    Expr (DeclareSignal label kind wirety flow width sense required (SYSTEM n) defaultValue doc idx)

  system m (Expr (Replicate n label kind wirety flow width sense required origin defaultValue doc idx)) =
    Expr (Replicate n label kind wirety flow width sense required (SYSTEM m) defaultValue doc idx)

  fromEither : LangM m () (LangIDL labelTy) (TyExpr DECL) old newK
            -> LangM m () (LangIDL labelTy) (TyExpr DECL) old newK
  fromEither (Expr (DeclareSignal label kind wirety flow width sense required origin defaultValue doc idx)) =
    Expr (DeclareSignal label kind wirety PCCP width sense required origin defaultValue doc idx)
  fromEither (Expr (Replicate n label kind wirety flow width sense required origin defaultValue doc idx)) =
    Expr (Replicate n label kind wirety PCCP width sense required origin defaultValue doc idx)

  fromInitiator : LangM m () (LangIDL labelTy) (TyExpr DECL) old newK
               -> LangM m () (LangIDL labelTy) (TyExpr DECL) old newK
  fromInitiator (Expr (DeclareSignal label kind wirety flow width sense required origin defaultValue doc idx)) =
    Expr (DeclareSignal label kind wirety PC width sense required origin defaultValue doc idx)
  fromInitiator (Expr (Replicate n label kind wirety flow width sense required origin defaultValue doc idx)) =
    Expr (Replicate n label kind wirety PC width sense required origin defaultValue doc idx)

  fromTarget : LangM m () (LangIDL labelTy) (TyExpr DECL) old newK
            -> LangM m () (LangIDL labelTy) (TyExpr DECL) old newK
  fromTarget (Expr (DeclareSignal label kind wirety flow width sense required origin defaultValue doc idx)) =
    Expr (DeclareSignal label kind wirety CP width sense required origin defaultValue doc idx)
  fromTarget (Expr (Replicate n label kind wirety flow width sense required origin defaultValue doc idx)) =
    Expr (Replicate n label kind wirety CP width sense required origin defaultValue doc idx)

  fromInitiatorAlways : LangM m () (LangIDL labelTy) (TyExpr DECL) old newK
                     -> LangM m () (LangIDL labelTy) (TyExpr DECL) old newK
  fromInitiatorAlways (Expr (DeclareSignal label kind wirety flow width sense required origin defaultValue doc idx)) =
    Expr (DeclareSignal label kind wirety ConstP width sense required origin defaultValue doc idx)
  fromInitiatorAlways (Expr (Replicate n label kind wirety flow width sense required origin defaultValue doc idx)) =
    Expr (Replicate n label kind wirety ConstP width sense required origin defaultValue doc idx)

  fromTargetAlways : LangM m () (LangIDL labelTy) (TyExpr DECL) old newK
                  -> LangM m () (LangIDL labelTy) (TyExpr DECL) old newK
  fromTargetAlways (Expr (DeclareSignal label kind wirety flow width sense required origin defaultValue doc idx)) =
    Expr (DeclareSignal label kind wirety ConstC width sense required origin defaultValue doc idx)
  fromTargetAlways (Expr (Replicate n label kind wirety flow width sense required origin defaultValue doc idx)) =
    Expr (Replicate n label kind wirety ConstC width sense required origin defaultValue doc idx)

  opt : LangM m () (LangIDL labelTy) (TyExpr DECL) old newK
     -> LangM m () (LangIDL labelTy) (TyExpr DECL) old newK
  opt (Expr (DeclareSignal label kind wirety flow width sense required origin defaultValue doc idx)) =
    Expr (DeclareSignal label kind wirety flow width sense CompletelyOptional origin defaultValue doc idx)
  opt (Expr (Replicate n label kind wirety flow width sense required origin defaultValue doc idx)) =
    Expr (Replicate n label kind wirety flow width sense CompletelyOptional origin defaultValue doc idx)

  targetOpt : LangM m () (LangIDL labelTy) (TyExpr DECL) old newK
           -> LangM m () (LangIDL labelTy) (TyExpr DECL) old newK
  targetOpt (Expr (DeclareSignal label kind wirety flow width sense required origin defaultValue doc idx)) =
    Expr (DeclareSignal label kind wirety flow width sense ConsumerOptional origin defaultValue doc idx)
  targetOpt (Expr (Replicate n label kind wirety flow width sense required origin defaultValue doc idx)) =
    Expr (Replicate n label kind wirety flow width sense ConsumerOptional origin defaultValue doc idx)

  initiatorOpt : LangM m () (LangIDL labelTy) (TyExpr DECL) old newK
              -> LangM m () (LangIDL labelTy) (TyExpr DECL) old newK
  initiatorOpt (Expr (DeclareSignal label kind wirety flow width sense required origin defaultValue doc idx)) =
    Expr (DeclareSignal label kind wirety flow width sense ProducerOptional origin defaultValue doc idx)
  initiatorOpt (Expr (Replicate n label kind wirety flow width sense required origin defaultValue doc idx)) =
    Expr (Replicate n label kind wirety flow width sense ProducerOptional origin defaultValue doc idx)

  setSensitivity : (s : Sensitivity)
                -> LangM m () (LangIDL labelTy) (TyExpr DECL) old newK
                -> LangM m () (LangIDL labelTy) (TyExpr DECL) old newK
  setSensitivity s (Expr (DeclareSignal label kind wirety flow width _ required origin vorigin doc idx)) =
    Expr (DeclareSignal label kind wirety flow width s required origin vorigin doc idx)
  setSensitivity s (Expr (Replicate n label kind wirety flow width _ required origin vorigin doc idx)) =
    Expr (Replicate n label kind wirety flow width s required origin vorigin doc idx)

namespace Metadata

  setVendor : String -> LangM m () (LangIDL labelTy) (TyExpr MDATA) old (const old)
  setVendor v = setMetadata (\mdata => record {mvendor = Just v} mdata)


  setLibrary : String -> LangM m () (LangIDL labelTy) (TyExpr MDATA) old (const old)
  setLibrary v = setMetadata (\mdata => record {mlibrary = Just v} mdata)


  setName : String -> LangM m () (LangIDL labelTy) (TyExpr MDATA) old (const old)
  setName v = setMetadata (\mdata => record {mname = Just v} mdata)


  setVersion : String -> LangM m () (LangIDL labelTy) (TyExpr MDATA) old (const old)
  setVersion v = setMetadata (\mdata => record {mversion = Just v} mdata)


  setMaxInitiators : (maxp : Whole) -> LangM m () (LangIDL labelTy) (TyExpr MDATA) old (const old)
  setMaxInitiators m = setMetadata (\mdata => record {mmaxp = Just m} mdata)


  setMaxTargets : (maxc : Whole) -> LangM m () (LangIDL labelTy) (TyExpr MDATA) old (const old)
  setMaxTargets m = setMetadata (\mdata => record {mmaxc = Just m} mdata)


  setCommunicationStyle : CommStyle -> LangM m () (LangIDL labelTy) (TyExpr MDATA) old (const old)
  setCommunicationStyle v = setMetadata (\mdata => record {mcstyle = Just v} mdata)


  setDoc : (d   : String -> Either String (Edda SNIPPET))
        -> (src : String)
        -> LangM m () (LangIDL labelTy) (TyExpr MDATA) old (const old)
  setDoc d src = setMetadata (\mdata => record {mdoc = Just (newDocString src d)} mdata)


  (#) : LangM m () (LangIDL labelTy) (TyExpr DECL) old newK
     -> (LangM m () (LangIDL labelTy) (TyExpr DECL) old newK
       -> LangM m () (LangIDL labelTy) (TyExpr DECL) old newK)
     -> LangM m () (LangIDL labelTy) (TyExpr DECL) old newK
  (#) a f = f a
