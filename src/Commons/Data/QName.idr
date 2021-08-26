||| Lightweight representation of qualified names.
|||
||| TODO: Look at making names subject to user supplied predicates.
module Commons.Data.QName

import Commons.Text.Display

%default total
%access public export

data Ty = SIMPLE | QUALIFIED

data QName : (ty : Type) -> (shape : Ty) -> Type where
  BN : ty -> QName ty SIMPLE
  QN : ty -> QName ty shape -> QName ty QUALIFIED

fromList : (xs : List ty) -> (prf : NonEmpty xs) -> QName ty (if length xs > 1 then QUALIFIED else SIMPLE)
fromList (x :: []) IsNonEmpty = BN x
fromList (x :: (y :: xs)) IsNonEmpty with (nonEmpty xs)
  fromList (x :: (y :: xs)) IsNonEmpty | (Yes prf) =  QN x $ QN y $ fromList xs prf
  fromList (x :: (y :: xs)) IsNonEmpty | (No contra) = QN x $ BN y

fromList' : (xs : List ty)
         -> {auto prf : NonEmpty xs}
         -> QName ty (if length xs > 1 then QUALIFIED else SIMPLE)
fromList' xs {prf} = fromList xs prf


Show ty => Show (QName ty shape) where
  show (BN x)    = unwords ["BN", show x]
  show (QN x xs) = unwords ["QN", show x, show xs]

Display ty => Display (QName ty shape) where
  display (BN x) = display x
  display (QN x ys) = display x ++ "." ++ display ys

-- --------------------------------------------------------------------- [ EOF ]
