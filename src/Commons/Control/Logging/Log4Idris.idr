module Commons.Control.Logging.Log4Idris

import Control.IOExcept
import Control.ST

%default total
%access export

public export
data LogLevel : Type where
  OFF : LogLevel

  ||| A fine-grained debug message, typically capturing the flow through
  ||| the application.
  TRACE : LogLevel

  ||| A general debugging event.
  DEBUG : LogLevel

  |||  An event for informational purposes.
  INFO : LogLevel

  ||| An event that might possible lead to an error.
  WARN : LogLevel

  ||| An error in the application, possibly recoverable.
  ERROR : LogLevel

  ||| A severe error that will prevent the application from continuing.
  FATAL : LogLevel

  ||| All events should be logged.
  ALL : LogLevel

export
Cast LogLevel Nat where
  cast OFF   = 0
  cast TRACE = 10
  cast DEBUG = 20
  cast INFO = 30
  cast WARN = 40
  cast ERROR = 50
  cast FATAL = 60
  cast ALL = 70

export
Eq LogLevel where
  (==) x y = cast {to=Nat} x == cast {to=Nat} y

export
Ord LogLevel where
  compare x y = compare (cast {to=Nat} x) (cast {to=Nat} y)

public export
interface Logging (m : Type -> Type) where
  Logger : Type

  startLogging : (lvl : LogLevel)
              -> ST m (Var) [add Logger]

  setLevel : (logger : Var)
          -> (n : LogLevel)
          -> ST m () [logger ::: Logger]

  log : (logger : Var)
     -> (lvl    : LogLevel)
     -> (msg    : String)
     -> ST m () [logger ::: Logger]

  endLogging : (logger : Var)
            -> ST m () [remove logger Logger]

public export
Logging IO where
  Logger = State LogLevel

  startLogging lvl = do
    logger <- new lvl
    pure logger

  setLevel logger n = write logger n

  log logger lvl msg = do
    curr <- read logger
    case compare lvl curr of
      GT => pure ()
      _  => do
        putStr $ unwords [show (cast {to=Nat} lvl), ":", msg]
        pure ()

  endLogging logger = delete logger

public export
Logging (IOExcept err) where
  Logger = State LogLevel

  startLogging lvl = do
    logger <- new lvl
    pure logger

  setLevel logger new = write logger new

  log logger lvl msg = do
    curr <- read logger
    case compare lvl curr of
      GT => pure ()
      _  => do
        putStr $ unwords [show (cast {to=Nat} lvl), ":", msg]
        pure ()

  endLogging logger = delete logger


-- --------------------------------------------------------------------- [ EOF ]
