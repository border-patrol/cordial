module Commons.System

import System

import Control.IOExcept
import Control.ST

import Data.So

public export
interface SystemIO (m : Type -> Type) where
  getArgs : STrans m (List String) xs (const xs)
  time    : STrans m Integer       xs (const xs)
  usleep  : (i : Int)
         -> {auto prf : So (i >= 0)}
         -> STrans m () xs (const xs)

export
SystemIO IO where
  getArgs = lift getArgs
  time    = lift time
  usleep i {prf} = lift $ usleep i {prf=prf}

-- --------------------------------------------------------------------- [ EOF ]
