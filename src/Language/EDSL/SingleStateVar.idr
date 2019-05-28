module Language.EDSL.SingleStateVar

import Data.List
import Data.List.Quantifiers

%default total
%access public export

namespace TypeLevel

  data Var : Type where
    MkVar : Var

  record StateItem (stateType : Type) where
    constructor MkStateItem
    label : Var
    value : stateType

  Context : (type : Type) -> Type
  Context type = List (StateItem type)


  Lang : Type -> Type -> Type
  Lang mtype stype = (val : mtype)
      -> (ty : Type)
      -> (pre : Context stype)
      -> (post : ty -> Context stype)
      -> Type

  data LANG : (mType : Type) -> (stype : Type) -> Type where
    MkLang : (mType : Type)
          -> (stype : Type)
          -> (rtype : Type)
          -> Lang mType stype
          -> LANG mType stype

  realType : LANG mType stateType -> Type
  realType (MkLang _ _ t  _) = t

  desc : LANG mType stateType -> Lang mType stateType
  desc (MkLang _ _ _ l) = l

  data LangTyM : Type -> Type where
    TyExpr : (ty : type) -> LangTyM type
    TyStmt : LangTyM type

  data LangM : (m : Type -> Type)
            -> (retTy : Type)
            -> (spec : LANG mType stype)
            -> (metaTy : LangTyM mType)
            -> (pre : Context stype)
            -> (post : retTy -> Context stype)
            -> Type
    where
      Value : (value : a) -> LangM m a spec TyStmt (postK value) postK

      Let : LangM m a spec mTyA old oldK
        -> ((val : a) -> LangM m b spec mTyB (oldK val) postK)
        -> LangM m b spec TyStmt old postK

      Expr : {eSig : Lang mType stype}
          -> (expr : eSig val t old newK)
          -> LangM m t (MkLang mType stype rtype eSig) (TyExpr val) old newK



namespace API
  pure : (value : a) -> LangM m a spec TyStmt (postK value) postK
  pure = Value

  (>>=) : LangM m a spec mTyA old oldK
        -> ((val : a) -> LangM m b spec mTyB (oldK val) postK)
        -> LangM m b spec TyStmt old postK
  (>>=) = Let

  expr : {eSig : Lang mtype stype}
      -> (expr : eSig val t old newK)
      -> LangM m t (MkLang mtype stype rtype eSig) (TyExpr val) old newK
  expr = Expr

namespace All
    AllContext : (p : StateItem type -> Type)
              -> (c : Context type)
              -> Type
    AllContext p c = All p c


namespace Element
  InContext : (p : StateItem type -> Type)
           -> (c : Context type)
           -> Type
  InContext p c = Any p c

  update : {predicate : StateItem type -> Type}
        -> (f : (item   : StateItem type)
             -> (bewijs : predicate item)
             -> StateItem type)
        -> (context : Context type)
        -> (index   : InContext predicate context)
        -> Context type
  update f (item :: rest) (Here bewijs) = f item bewijs :: rest
  update f (not_x :: rest) (There komt) = not_x :: update f rest komt

  drop : {predicate : StateItem type -> Type}
      -> (context   : Context type)
      -> (index     : InContext predicate context)
      -> Context type
  drop (item :: rest) (Here bewijs) = rest
  drop (not_x :: rest) (There komt) = not_x :: drop rest komt

  setState : {predicate : StateItem type -> Type}
          -> (item'     : type)
          -> (context   : Context type)
          -> (index     : InContext predicate context)
          -> Context type
  setState item' context index {predicate} {type} =
       update (doUpdate item') context index
    where
      doUpdate : (newState : type)
              -> (item     : StateItem type)
              -> (bewijs   : predicate item)
              -> StateItem type
      doUpdate newState (MkStateItem label state) bewijs = (MkStateItem label newState)

-- -------------------------------------------------------------- [ Evaluation ]
namespace Env
  data Tag : LANG mtype stype ->  Type where
    MkTag : (real : rtype) -> Tag (MkLang mtype stype rtype eSig)

  data Env : (m : Type -> Type) -> LANG mtype stype -> Context stype -> Type where
    Nil  : Env m spec Nil
    (::) : (tag  : Tag spec)
        -> (rest : Env m spec items)
        -> Env m spec (item::items)

  lookup : (env : Env m lang context)
        -> (idx : InContext p context)
        -> Tag lang
  lookup (tag :: rest) (Here prf) = tag
  lookup (tag :: rest) (There later) = lookup rest later

  ||| Update the type level state in the environment.
  update : {ctxt : Context stype}
        -> (env  : Env m lang ctxt)
        -> (idx  : InContext p ctxt)
        -> (up   : (i : StateItem stype) -> p i -> StateItem stype)
        -> Env m lang (update up ctxt idx)
  update (tag :: rest) (Here prf) up = tag :: rest
  update (tag :: rest) (There later) up = tag :: update rest later up

  ||| Drop the state at the given index.
  drop : (env : Env m lang ctxt)
      -> (idx : InContext p ctxt)
      -> Env m lang (drop ctxt idx)
  drop (tag :: rest) (Here prf) = rest
  drop (tag :: rest) (There later) = tag :: drop rest later


namespace Building

  interface Builder (l : LANG mtype stype) (tyBRes : Type) (m : Type -> Type) | l where
     build : (env  : Env m l pre)
          -> (expr : (desc l) val tyExpr pre postK)
          -> (acc  : tyBRes)
          -> (cont : (value' : tyExpr)
                  -> (env' : Env m l (postK value'))
                  -> (acc' : tyBRes)
                  -> m tyRes)
          -> m tyRes

  rawEval : Builder lang tyBRes m
         => (env  : Env m lang pre)
         -> (expr : LangM m tyExpr lang mty pre postK)
         -> (acc  : tyBRes)
         -> (cont : (value : tyExpr)
                 -> (env'  : Env m lang (postK value))
                 -> (acc'  : tyBRes)
                 -> m tyRes)
         -> m tyRes
  rawEval env (Value value) acc cont = cont value env acc
  rawEval env (Let this beIn) acc cont =
    rawEval env this acc (\this', env', acc' =>
                             rawEval env' (beIn this') acc' cont)
  rawEval env (Expr expr) acc cont =
     build env expr acc (\value', env', acc' => cont value' env' acc')

  record BuildResult (tyExpr : Type) (tyBRes : Type) where
    constructor MkResult
    computed : tyExpr
    built    : tyBRes

  runBuild : Applicative m
          => Builder lang tyBRes m
          => (init : tyBRes)
          -> (expr : LangM m tyExpr lang mTy Nil (const Nil))
          -> m (BuildResult tyExpr tyBRes)
  runBuild init expr = rawEval Nil expr init (\val, env', acc' => pure $ MkResult val acc')

  runPure : Builder lang tyBRes Basics.id
         => (init : tyBRes)
         -> (expr : LangM Basics.id tyExpr lang mTy Nil (const Nil))
         -> (BuildResult tyExpr tyBRes)
  runPure init expr = rawEval Nil expr init (\val, env', acc' => MkResult val acc')

-- --------------------------------------------------------------------- [ EOF ]
