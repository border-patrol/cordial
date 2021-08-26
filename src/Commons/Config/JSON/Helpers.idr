module Commons.Config.JSON.Helpers

import Data.PList

import Commons.Config.JSON.Model

%access public export
%default total

data ParseResult : Type where
  PR : (ty : JTy)
    -> (value : JSONDoc ty)
    -> (prf   : JPred ty)
    -> ParseResult

data ArrayResult : List JTy -> Type where
  SR : DList JTy JSONDoc as
    -> DList JTy JPred as
    -> ArrayResult as

combineAsArray : List ParseResult -> (as ** ArrayResult as)
combineAsArray [] = (_ ** SR Nil Nil)
combineAsArray (x :: xs) with (x)
  combineAsArray (x :: xs) | (PR ty value prf) with (combineAsArray xs)
    combineAsArray (x :: xs) | (PR ty value prf) | (as ** pf) with (pf)
      combineAsArray (x :: xs) | (PR ty value prf) | (as ** pf) | (SR rest prfs) =
        (ty ::as ** SR (value::rest) (prf :: prfs))

toArray : List ParseResult -> JSONDoc ARRAY
toArray ps with (combineAsArray ps)
  toArray ps | (x ** prf) with (prf)
    toArray ps | (x ** prf) | (SR rest y) =
      JArray (fromDList rest y)

data DictResult : List JTy -> Type where
  DR : DList JTy (\ty => Pair String (JSONDoc ty)) as
    -> DList JTy JPred as
    -> DictResult as

combineAsDict : List (String, ParseResult)
             -> (as ** DictResult as)
combineAsDict [] = (_ ** DR Nil Nil)
combineAsDict ((a, b) :: xs) with (b)
  combineAsDict ((a, b) :: xs) | (PR ty value prf) with (combineAsDict xs)
    combineAsDict ((a, b) :: xs) | (PR ty value prf) | (x ** pf) with (pf)
      combineAsDict ((a, b) :: xs) | (PR ty value prf) | (x ** pf) | (DR rest y) =
        (ty :: x ** DR (MkPair a value::rest) (prf :: y))



toDict : List (String, ParseResult) -> JSONDoc MAP
toDict xs with (combineAsDict xs)
  toDict xs | (x ** pf) with (pf)
    toDict xs | (x ** pf) | (DR rest y) =
      JMap (fromDList rest y)
