module Text.Markup.Edda.Process.Shunt

import Data.AVL.Dict
import Data.Stack
import Data.List.Views

import Text.Markup.Edda.Model.Common
import Text.Markup.Edda.Model.Processed

%access private
%default total

-- @ TODO make more precise.

data SecInfo : Type where
  MkSInfo : (depth : Nat)
         -> (label : Maybe String)
         -> (title : List (Edda INLINE))
         -> (attrs : Dict String String)
         -> (body  : List (Edda BLOCK))
         -> SecInfo
  NoInfo : SecInfo

popThings : Nat -> List (Edda BLOCK)
                -> List (Edda BLOCK)
                -> (List (Edda BLOCK), List (Edda BLOCK))
popThings k xs Nil = (xs, Nil)
popThings k xs ((Section d l t as b)::ys) with (compare d k)
  popThings k xs ((Section d l t as b)::ys) | LT = (xs, Section d l t as b :: ys)
  popThings k xs ((Section d l t as b)::ys) | _ = popThings k (xs ++ [Section d l t as b]) ys

popThings k xs (block::ys) = popThings k (xs ++ [block]) ys



performShunt : (stack  : Stack (Edda BLOCK))
            -> (output : List (Edda BLOCK))
            -> (input : List (Edda BLOCK))
            -> List (Edda BLOCK)
performShunt stack output input with (snocList input)
  performShunt stack output [] | Empty = stack ++ output
  performShunt stack output (xs ++ [x]) | (Snoc rec) with (x)
    performShunt stack output (xs ++ [x]) | (Snoc rec) | (Section depth label title attrs body) with (output)
      performShunt stack output (xs ++ [x]) | (Snoc rec) | (Section depth label title attrs body) | [] =
        performShunt mkStack [Section depth label title attrs (body ++ stack)] xs | rec
      performShunt stack output (xs ++ [x]) | (Snoc rec) | (Section depth label title attrs body) | (y :: ys) with (y)

        performShunt stack output (xs ++ [x]) | (Snoc rec) | (Section depth label title attrs body) | (y :: ys) | (Section k z zs w ws) with (compare depth k)
          performShunt stack output (xs ++ [x]) | (Snoc rec) | (Section depth label title attrs body) | (y :: ys) | (Section k z zs w ws) | LT =
              let (ls,rs) = popThings k Nil (output) in
               performShunt mkStack ([Section depth label title attrs (body ++ stack ++ ls)] ++ rs) xs | rec
          performShunt stack output (xs ++ [x]) | (Snoc rec) | (Section depth label title attrs body) | (y :: ys) | (Section k z zs w ws) | GT =

              performShunt mkStack ([Section depth label title attrs (body ++ stack)] ++ output) xs | rec
          performShunt stack output (xs ++ [x]) | (Snoc rec) | (Section depth label title attrs body) | (y :: ys) | (Section k z zs w ws) | EQ =
              performShunt mkStack ([Section depth label title attrs (body ++ stack)] ++ output) xs | rec

        performShunt stack output (xs ++ [x]) | (Snoc rec) | (Section depth label title attrs body) | (y :: ys) | block =
          performShunt mkStack ([Section depth label title attrs (body ++ stack)] ++ output) xs | rec

    performShunt stack output (xs ++ [x]) | (Snoc rec) | block = performShunt (pushS block stack) output xs | rec


export
shunt : List (Edda BLOCK) -> List (Edda BLOCK)
shunt = performShunt Nil Nil

-- --------------------------------------------------------------------- [ EOF ]
