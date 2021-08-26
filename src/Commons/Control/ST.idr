module Commons.ST

import Control.ST

import Commons.Data.Action

%default total
%access public export

addIfResult : Type -> Action (Action RESULT ety Var)
addIfResult ty = Add (result Nil (\var => [var ::: ty]))

onAction : a -> a -> Action aty ety rty -> a
onAction x y Success    = x
onAction x y (Result _) = x
onAction x y (Error _)  = y


-- --------------------------------------------------------------------- [ EOF ]
