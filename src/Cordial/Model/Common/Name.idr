module Cordial.Model.Common.Name

%default total
%access public export

data NameKind = WHOLE | INDEXED | ANY

data Name : (kind : NameKind) -> (type : Type) -> Type where
  WName : List String -> type -> Name WHOLE type
  IName : List String -> type -> Nat -> Name INDEXED type
  NoName : Name ANY type
