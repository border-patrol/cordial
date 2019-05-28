||| This modules presents an exemplar specification 'Mungo'
||| demonstrating salient features of the abstract interfact
||| description language.
module Example.Specification.Mungo

import Text.Markup.Edda
import Text.Markup.Edda.Org

import Cordial.EDSL.Specification

%access public export
%default total

||| Concrete labels for port descriptions.
data MTy = CLOCK
         | WRITE
         | READ
         | ADDRESS
         | DATA
         | ERROR_MODE
         | ERROR_INFO

||| Equality type is required to differentiate labels.
Eq MTy where
  (==) CLOCK      CLOCK      = True
  (==) WRITE      WRITE      = True
  (==) READ       READ       = True
  (==) ADDRESS    ADDRESS    = True
  (==) DATA       DATA       = True
  (==) ERROR_MODE ERROR_MODE = True
  (==) ERROR_INFO ERROR_INFO = True
  (==) _ _ = False

||| This function represents the 'generic' specification for Mungo.
|||
||| @dWidth The width of the data bus.
||| @aWidth The width of addresses
Mungo_Gen : (dWidth : Nat)
         -> (aWidth : Nat)
         -> (prfD  : ValidArraySpec dWidth [32,16])
         -> (prfA  : ValidArraySpec aWidth [8,4])
         -> IDL MTy
Mungo_Gen dWidth aWidth prfD prfA = do
  setVendor "cs.glasgow.ac.uk"
  setLibrary "examples"
  setName ("Mungo"
    <+> "_"
    <+> show dWidth
    <+> "_"
    <+> show aWidth
    <+> "_Description")
  setVersion "0.1"
  setCommunicationStyle Unicast

  c <- label CLOCK
  w <- label WRITE
  r <- label READ
  e <- label ERROR_MODE
  i <- label ERROR_INFO
  a <- label ADDRESS
  d <- label DATA

  clock c Nothing Nothing Nothing
    # system "SYS"
    # fromTargetAlways

  control w # fromInitiator

  control r # fromInitiator

  info e (fromNat 2)  # fromTarget
                      # targetOpt

  info i # fromTarget
         # targetOpt

  address a (fromNat aWidth prfA) # fromInitiator

  bus d (fromNat dWidth prfD) # fromEither

  stop


||| Transform the specification into a model.
Mungo : (dWidth, aWidth : Nat)
     -> {auto prfD : ValidArraySpec dWidth [32,16]}
     -> {auto prfA : ValidArraySpec aWidth [8,4]}
     -> InterfaceTy () MTy
Mungo dWidth aWidth {prfD} {prfA} =
  buildSpec (Mungo_Gen dWidth aWidth prfD prfA)

-- Some sample instances.

Mungo_32_4 : InterfaceTy () MTy
Mungo_32_4 = Mungo 32 4

Mungo_16_8 : InterfaceTy () MTy
Mungo_16_8 = Mungo 16 8

-- --------------------------------------------------------------------- [ EOF ]
