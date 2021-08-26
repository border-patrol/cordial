module Commons.Control.File

import Control.ST

import Commons.Control.ST

import Commons.Data.Action

%access public export
%default total

-- -------------------------------------------------------------- [ Predicates ]

||| A record of the file modes that can read from a file.
data ValidModeRead : Mode -> Type where
  VMRRead   : ValidModeRead Read
  VMRReadW  : ValidModeRead ReadWrite
  VMRReadWT : ValidModeRead ReadWriteTruncate
  VMRReadA  : ValidModeRead ReadAppend

||| A record of the file modes that can write from a file.
data ValidModeWrite : Mode -> Type where
  VMWWrite  : ValidModeWrite WriteTruncate
  VMWAppend : ValidModeWrite Append
  VMWReadW  : ValidModeWrite ReadWrite
  VMWReadWT : ValidModeWrite ReadWriteTruncate

data State = Closed | Open

-- -------------------------------------------------- [ Custom Error Reporting ]

||| Alias for File actions.
FileAction : ActionTy -> Type -> Type
FileAction action = Action action FileError

interface FileIO (m : Type -> Type) where
  data File : Mode -> State -> Type

  open : (fname : String)
      -> (fmode : Mode)
      -> ST m (FileAction RESULT Var) [addIfResult $ File fmode Open]

  openX : (fname : String)
       -> (fmode : Mode)
       -> ST m (FileAction RESULT Var) [addIfResult $ File fmode Open]

  close : (fh : Var)
        -> ST m () [Remove fh (File fm st)]

  readChar : (fh : Var)
          -> {auto prf : ValidModeRead fm}
          -> ST m (FileAction RESULT Char)
                  [fh ::: File fm Open :-> onAction (File fm Open) (File fm Closed)]

  readLine : (fh : Var)
          -> {auto prf : ValidModeRead fm}
          -> ST m (FileAction RESULT String)
                  [fh ::: File fm Open :-> onAction (File fm Open) (File fm Closed)]

  readFile : (fname : String)
          -> STrans m (FileAction RESULT String) xs (const xs)

  writeStr : (fh : Var)
          -> (str : String)
          -> {auto prf : ValidModeWrite fm}
          -> ST m (FileAction SUCCESS ())
                  [fh ::: File fm Open :-> onAction (File fm Open) (File fm Closed)]

  writeLine : (fh : Var)
           -> (str : String)
           -> {auto prf : ValidModeWrite fm}
           -> ST m (FileAction SUCCESS ())
                   [fh ::: File fm Open :-> onAction (File fm Open) (File fm Closed)]

  writeFile : (fname : String)
           -> (str : String)
           -> STrans m (FileAction SUCCESS ()) xs (const xs)

  -- misc
  flush : (fh : Var)
       -> ST m () [fh ::: File fm Open]

  eof : (fh : Var)
     -> ST m Bool [fh ::: File fm Open]

FileIO IO where
  File x y = State File

  open fname fmode = do
    res <- lift $ openFile fname fmode
    case res of
      Left err => pure $ Error err
      Right fh => do
        v <- new fh
        pure $ Result v

  openX fname fmode = do
    res <- lift $ openFileX fname fmode
    case res of
      Left err => pure $ Error err
      Right fh => do
        v <- new fh
        pure $ Result v

  close v = do
     fh  <- read v
     lift $ closeFile fh
     delete v
     pure ()


  readChar var = do
      fh <- read var
      case !(lift $ fgetc fh) of
        Left err => pure $ Error err
        Right ln => pure $ Result ln

  readLine var = do
    fh <- read var
    case !(lift $ fGetLine fh) of
      Left err => pure $ Error err
      Right ln => pure $ Result ln

  readFile fname = do
    case !(lift $ readFile fname) of
      Left err  => pure $ Error err
      Right str => pure $ Result str


  writeStr var str = do
    fh <- read var
    case !(lift $ fPutStr fh str) of
      Left err => pure $ Error err
      Right _  => pure $ Success

  writeLine var str = do
    fh <- read var
    case !(lift $ fPutStrLn fh str) of
      Left err => pure $ Error err
      Right _  => pure $ Success

  writeFile fname str = do
    case !(lift $ writeFile fname str) of
      Left err => pure $ Error err
      Right  _ => pure $ Success

  flush var = do
    fh <- read var
    res <- lift $ fflush fh
    pure res

  eof var = do
    fh <- read var
    res <- lift $ fEOF fh
    pure res

-- --------------------------------------------------------------------- [ EOF ]
