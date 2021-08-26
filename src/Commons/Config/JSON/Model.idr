module Commons.Config.JSON.Model

import Data.PList

%default total
%access public export

data JTy = DOC | ARRAY | MAP | VALUE

data JPred : JTy -> Type where
  ValidMap : JPred MAP
  ValidArr : JPred ARRAY
  ValidVal : JPred VALUE

data JSONDoc : JTy -> Type where
  JStr : String -> JSONDoc VALUE
  JNum : Double  -> JSONDoc VALUE
  JBool : Bool  -> JSONDoc VALUE

  JNull : JSONDoc VALUE

  JArray : PList JTy JSONDoc JPred as prfs -> JSONDoc ARRAY
  JMap : PList JTy (\ty => (String, JSONDoc ty)) JPred as prfs -> JSONDoc MAP

  JDoc : (ty : JTy) -> JSONDoc ty -> JSONDoc DOC
