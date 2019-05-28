module Cordial.EDSL.Description.Lang

import Data.Vect
import Data.List.Quantifiers
import Data.Ranged

import Text.Markup.Edda

import Language.EDSL.SingleStateVar

import Cordial.Model.Specification

%default total
%access public export

-- ------------------------------------------------- [ Important Language Defs ]

data Used = FREE | USED

||| State associated with labels.
record State (labelType : Type) where
  constructor MkState
  used  : Used
  label : labelType

VarState : Type -> Type
VarState labelTy = StateItem (State labelTy)

Gamma : Type -> Type
Gamma labelTy = Context (State labelTy)

-- -------------------------------------------------------------- [ Predicates ]

namespace Predicates

  data CanUseVar : (labelTy : Type) -> Var -> VarState labelTy -> Type where
    FreeName : CanUseVar type lbl (MkStateItem lbl $ MkState FREE val)

  data UsedVar : (labelTy : Type) -> VarState labelTy -> Type where
    NameIsUsed : UsedVar type (MkStateItem lbl $ MkState USED val)

  VarsAllUsed : (labelTy : Type) -> (ctxt : Gamma labelTy) -> Type
  VarsAllUsed labelTy ctxt =
    AllContext (UsedVar labelTy) ctxt

  data VarIsNotNamed : (labelTy : Type)
                    -> (label : labelTy)
                    -> VarState labelTy
                    -> Type where
    IsNotNamed : Eq labelTy
              => {l,r : labelTy}
              -> (prf : l /= r = True)
              -> VarIsNotNamed labelTy l (MkStateItem lbl (MkState u r))

  CanUseName : (label : labelTy) -> (ctxt : Gamma labelTy) -> Type
  CanUseName {labelTy} label =
    AllContext (VarIsNotNamed labelTy label)

-- ----------------------------------------------------------------- [ Updates ]

namespace Functions
  Consume : (item : VarState labelTy)
         -> (bewijs : CanUseVar labelTy lbl item)
         -> VarState labelTy
  Consume item bewijs with (bewijs)
    Consume (MkStateItem lbl (MkState FREE val)) bewijs | FreeName =
      MkStateItem lbl (MkState USED val)


-- ------------------------------------------------------------- [ Expressions ]

record Metadata where
  constructor MkMetadata
  mvendor  : Maybe String
  mlibrary : Maybe String
  mname    : Maybe String
  mversion : Maybe String
  mmaxp    : Maybe Whole
  mmaxc    : Maybe Whole
  mcstyle  : Maybe CommStyle
  mdoc     : Maybe DocString

processMetadata : Metadata -> (VLNV, (Whole, Whole), CommStyle, DocString)
processMetadata (MkMetadata mvendor mlibrary mname mversion mmax mmin mcstyle mdoc) =
  let vlnv = MkVLNV (fromMaybe "Default Vendor" mvendor)
                    (fromMaybe "Default Library" mlibrary)
                    (fromMaybe "Default Name" mname)
                    (fromMaybe "Default Version" mversion) in
  let a = (fromMaybe (fromNat 1) mmin, fromMaybe (fromNat 1) mmax) in
  let c = fromMaybe Unicast mcstyle in
  let d = fromMaybe Empty mdoc in
    (vlnv, a,c,d)

defaultMetadata : Metadata
defaultMetadata =
  MkMetadata
     Nothing
     Nothing
     Nothing
     Nothing
     Nothing
     Nothing
     Nothing
     Nothing

data ExprTy = DECL | MDATA | NAME | END

data IDescribe : (labelTy : Type) -> Lang ExprTy (State labelTy) where
   NewName : (name : labelTy)
          -> (prf  : CanUseName name old)
          -> IDescribe labelTy NAME Var old (\lbl => MkStateItem lbl (MkState FREE name)::old)

   Stop : (prf : VarsAllUsed labelTy old)
       -> IDescribe labelTy END () old (const Nil)

   SetMetadata : (Metadata -> Metadata)
              -> IDescribe labelTy MDATA () old (const old)

   DeclareSignal : (label  : Var)
                -> (kind  : PortShape)
                -> (wirety : WireTy)
                -> (flow  : Flow)
                -> (width : PortWidthDesc kind)

                -> (sense : Sensitivity)

                -> (required : OptionalTy)
                -> (origin   : Origin)

                -> (vorigin : ValueOrigin width)
                -> (doc : DocString)

                -> (prf : InContext (CanUseVar labelTy label) old)

                -> IDescribe labelTy DECL () old (const $ update Consume old prf)

   Replicate : (n : Nat)
            -> (var : Var)
            -> (kind : PortShape)
            -> (wirety : WireTy)
            -> (flow  : Flow)
            -> (width : PortWidthDesc kind)

            -> (sense : Sensitivity)

            -> (required : OptionalTy)
            -> (origin   : Origin)

            -> (vorigin : ValueOrigin width)
            -> (doc : DocString)
            -> (prf : InContext (CanUseVar labelTy var) old)
            -> IDescribe labelTy DECL () old (const $ update Consume old prf)

LangIDL : (labelTy : Type) -> LANG ExprTy (State labelTy)
LangIDL labelTy = MkLang ExprTy
                         (State labelTy)
                         (Name WHOLE labelTy)
                         (IDescribe labelTy)

namespace API
  IDL' : (labelTy : Type) -> (m : Type -> Type) -> Type
  IDL' ty m = LangM m () (LangIDL ty) (TyStmt) Nil (const Nil)

  label : (name : labelTy)
         -> {auto prf : CanUseName name old}
         -> LangM m Var (LangIDL labelTy) (TyExpr NAME) old (\lbl => MkStateItem lbl (MkState FREE name)::old)
  label n {prf} = Expr $ NewName n prf

  stop : {auto prf : VarsAllUsed labelTy old}
      -> LangM m () (LangIDL labelTy) (TyExpr END) old (const Nil)
  stop {prf} = Expr (Stop prf)

  setMetadata : (Metadata -> Metadata) -> LangM m () (LangIDL labelTy) (TyExpr MDATA) old (const old)
  setMetadata f = Expr (SetMetadata f)

  signal : (label  : Var)
        -> (kind  : PortShape)
        -> (wirety : WireTy)
        -> (flow  : Flow)
        -> (width : PortWidthDesc kind)

        -> (sense : Sensitivity)

        -> (required : OptionalTy)
        -> (origin   : Origin)

        -> (vorigin : ValueOrigin width)
        -> (doc : DocString)

        -> (prf : InContext (CanUseVar labelTy label) old)
        -> LangM m () (LangIDL labelTy) (TyExpr DECL) old (const $ update Consume old prf)
  signal label kind wirety flow width sense required origin vorigin doc prf =
    Expr $ DeclareSignal label kind wirety flow width sense required origin vorigin doc prf

  replicateExpr : (n : Nat)
           -> (var : Var)
           -> (kind : PortShape)
           -> (wirety : WireTy)
           -> (flow  : Flow)
           -> (width : PortWidthDesc kind)

           -> (sense : Sensitivity)

           -> (required : OptionalTy)
           -> (origin   : Origin)

           -> (vorigin : ValueOrigin width)
           -> (doc : DocString)
           -> {auto prf : InContext (CanUseVar labelTy var) old}

           -> LangM m () (LangIDL labelTy) (TyExpr DECL) old (const $ update Consume old prf)
  replicateExpr n var kind wirety flow width sense required origin vorigin doc {prf} =
    Expr $ Replicate n var kind wirety flow width sense required origin vorigin doc prf

nCopies : (c : Nat)
       -> (n : Name WHOLE labelTy)
       -> (kind  : PortShape)
       -> (wirety : WireTy)
       -> (flow  : Flow)
       -> (width : PortWidthDesc kind)

       -> (sense : Sensitivity)

       -> (required : OptionalTy)
       -> (origin   : Origin)

       -> (vorigin : ValueOrigin width)
       -> (doc : DocString)
       -> PortGroupTy () labelTy
nCopies c (WName xs x) k ty f w s r o vo doc =
    map (\i => PortDesc () k (IName xs x i) ty f w s r o vo doc) (countdown c)
  where
    countdown : Nat -> List Nat
    countdown Z     = [Z]
    countdown (S j) = S j :: countdown j

namespace Pure
  Builder (LangIDL labelTy) (Metadata, PortGroupTy () labelTy) Basics.id where
    build env (NewName name prf) (mdata,pg) cont =
      cont MkVar (MkTag (WName Nil name) :: env) (mdata,pg)

    build env (Stop prf) (mdata, acc) cont =
      cont () Nil (mdata, acc)

    build env (SetMetadata f) (mdata,acc) cont =
      cont () env ((f mdata),acc)

    build env (DeclareSignal label kind wirety flow width sense required origin vorigin doc prf) (mdata,acc) cont with (lookup env prf)
      build env (DeclareSignal label kind wirety flow width sense required origin vorigin doc prf) (mdata,acc) cont | (MkTag (WName xs x)) =
        cont () (update env prf Consume) (mdata,(PortDesc () kind (WName xs x) wirety flow width sense required origin vorigin doc :: acc))

    build env (Replicate n var kind wirety flow width sense required origin vorigin doc prf) (mdata, acc) cont with (lookup env prf)
      build env (Replicate n var kind wirety flow width sense required origin vorigin doc prf) (mdata, acc) cont | (MkTag (WName xs x)) =
        let ports = nCopies n (WName xs x) kind wirety flow width sense required origin vorigin doc in
          cont () (update env prf Consume) (mdata, ports ++ acc)

  IDL : (labelTy : Type) -> Type
  IDL ty = IDL' ty Basics.id

  buildSpec : IDL labelTy
           -> InterfaceTy () labelTy
  buildSpec expr =
      let (MkResult () (mdata,ps)) = runPure (defaultMetadata, List.Nil) expr in
      let (vlnv, (minA, minB), cstyle, doc) = processMetadata mdata in
        MkInterfaceTy vlnv () cstyle minA minB ps Nil doc

-- --------------------------------------------------------------------- [ EOF ]
