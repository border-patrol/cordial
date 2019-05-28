module Cordial.Model.Common.VLNV

%default total
%access public export

record VLNV where
  constructor MkVLNV
  vendor : String
  library : String
  name    : String
  version : String

-- --------------------------------------------------------------------- [ EOF ]
