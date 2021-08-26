module Commons.Control.Logging.Logger

import Control.IOExcept
import Control.ST

import Data.AVL.Dict

%default total
%access export

public export
interface (Show ty, Eq ty, Ord ty) => LogElement ty where

public export
interface Logging (m : Type -> Type)
  where
    Logger : Type -> Type -> Type

    start : (LogElement e, LogElement c)
         => (levels     : List (e, Nat))
         -> (categories : List c)
         -> (formatter  : c -> e -> Nat -> String -> String)
         -> ST m Var [add $ Logger e c]

    stop : (logger : Var) -> ST m () [remove logger (Logger e c)]

    setCategories : (logger : Var)
                 -> (categories : List c)
                 -> ST m () [logger ::: Logger e c]

    setEventLoggingLevel : (LogElement e)
                        => (logger : Var)
                        -> (event  : e)
                        -> (level  : Nat)
                        -> ST m () [logger ::: Logger e c]

    getLoggingState : (logger : Var)
                   -> ST m (List (e, Nat), List c) [logger ::: Logger e c]

    log : (LogElement e, LogElement c)
       => (logger   : Var)
       -> (category : c)
       -> (event    : e)
       -> (level    : Nat)
       -> (message  : String)
       -> ST m () [logger ::: Logger e c]


record LoggingState x y where
  constructor MkState
  events     : Dict x Nat
  categories : List y
  formatter  : y -> x -> Nat -> String -> String

Logging IO where
  Logger x y = State (LoggingState x y)

  start levels categories formatter = do
    let startST = MkState (fromList levels) categories formatter
    logger <- new startST
    pure logger

  stop logger = delete logger

  setCategories logger cats =
    update logger (\st => record {categories = cats} st)

  setEventLoggingLevel logger event level =
    update logger (record {events $= (insert event level)})

  getLoggingState logger = do
    st <- read logger
    pure (toList (events st), categories st)

  log logger category event level msg = do
    st <- read logger
    let curr_lvl = fromMaybe Z (lookup event (events st))
    case compare level curr_lvl of
      GT => pure ()
      _  => do
        let can_log = elem category (categories st) || isNil (categories st)
        if not can_log
          then pure ()
          else putStrLn $ (formatter st) category event level msg

-- --------------------------------------------------------------------- [ EOF ]
