-- -------------------------------------------------------------- [ Common.idr ]
-- Module    : Common.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
module Text.Markup.Edda.Writer.Common

import Effects
import Effect.Exception
import Effect.File
import Effect.StdIO

import Text.Markup.Edda.Model

%access export
-- -------------------------------------------------------------------- [ Body ]

strFromMaybe : (a -> String) -> Maybe a -> String
strFromMaybe f Nothing  = "EMPTY"
strFromMaybe f (Just x) = f x

writeEddaFileE : (Edda DOC -> String)
              -> String
              -> Edda DOC
              -> Eff (FileOpSuccess) [FILE ()]
writeEddaFileE write fname doc = writeFile fname (write doc)

writeEddaFile : (Edda DOC -> String)
             -> String
             -> Edda DOC
             -> IO (Either FileError ())
writeEddaFile write fname doc = writeFile fname (write doc)

-- --------------------------------------------------------------------- [ EOF ]
