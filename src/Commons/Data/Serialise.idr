-- ----------------------------------------------------------- [ Serialise.idr ]
||| Module    : Serialise.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
||| How to serialise objects between two different types. A slightly
||| more sane version of `Cast`.
|||
||| We could call this class marshall but I am fond of the
||| connotations associated with Java's serializable interface.
module Commons.Data.Serialise

%access public export

-- ------------------------------------------------------------------ [ Errors ]

data SerialiseError : Type where
  EmptyString    : SerialiseError
  MalformedData  : (msg : String) -> (raw : String) -> SerialiseError
  IncompleteData : (msg : String) -> (raw : String) -> SerialiseError
  ReadingError   : (msg : String) -> (raw : String) -> SerialiseError

Show SerialiseError where
    show EmptyString              = "Given an empty string."
    show (MalformedData msg raw)  = unlines ["Malformed Data Error:",  msg, "Raw String:", raw]
    show (IncompleteData msg raw) = unlines ["Incomplete Data Error:", msg, "Raw String:", raw]
    show (ReadingError msg raw)   = unlines ["Reading Error:",         msg, "Raw String:", raw]

-- -------------------------------------------------------------- [ Definition ]

||| Serialise data of type `a` to data of type `b`.
interface Serialise a b where
  writeData : a -> b
  readData  : b -> Either SerialiseError a

-- ---------------------------------------------------------- [ Some instances ]

Serialise a a where
    writeData x = x
    readData  x = Right x

Serialise Int String where
  writeData x = show x
  readData  x = Right $ cast x

Serialise Nat String where
  writeData x = show x
  readData  x = Right $ cast x

Serialise Double String where
  writeData x = show x
  readData  x = Right $ cast x

Serialise Integer String where
  writeData x = show x
  readData  x = Right $ cast x

-- --------------------------------------------------------------------- [ EOF ]
