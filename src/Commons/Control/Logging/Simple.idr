module Commons.Control.Logging.Simple

import Control.ST

public export
interface Logging (m : Type -> Type) where
  Logger : Type

  startLogging : (lvl : Nat)
              -> ST m (Var) [add Logger]

  setLevel : (logger : Var)
          -> (lvl : Nat)
          -> ST m () [logger ::: Logger]

  log : (logger : Var)
     -> (lvl    : Nat)
     -> (msg    : String)
     -> ST m () [logger ::: Logger]

  endLogging : (logger : Var)
            -> ST m () [Remove logger Logger]

public export
Logging IO where
  Logger = State Nat

  startLogging lvl = do
    logger <- new lvl
    pure logger

  setLevel logger new = write logger new

  log logger lvl msg = do
    curr <- read logger
    case compare lvl curr of
      GT => pure ()
      _  => do
        putStr $ unwords ["[", show lvl, "]", msg]
        pure ()

  endLogging logger = delete logger


-- --------------------------------------------------------------------- [ EOF ]
