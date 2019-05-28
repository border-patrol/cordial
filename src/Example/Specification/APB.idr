||| This module presents a realisation of ARMs APB protocol using our
||| abstract interface definition language.
module Example.Specification.APB

import Text.Markup.Edda
import Text.Markup.Edda.Org

import Cordial.EDSL.Specification

%access public export
%default total

||| Concrete labels for port descriptions.
data APBRTy = CLOCK | RESET | ADDR | PROT | SELECT
            | ENABLE | WRITE | WDATA | STROBE | READY
            | RDATA | ERROR

||| Equality type is required to differentiate labels.
Eq APBRTy where
  (==) CLOCK  CLOCK  = True
  (==) RESET  RESET  = True
  (==) ADDR   ADDR   = True
  (==) PROT   PROT   = True
  (==) SELECT SELECT = True
  (==) ENABLE ENABLE = True
  (==) WRITE  WRITE  = True
  (==) WDATA  WDATA  = True
  (==) STROBE STROBE = True
  (==) READY  READY  = True
  (==) RDATA  RDATA  = True
  (==) ERROR  ERROR  = True
  (==) _      _      = False

namespace Initiator
  ||| This function represents the abstract interface description for
  ||| APBs initiating interface.
  |||
  ||| This interface connect is designed to be connected to a single
  ||| interconnect component, which in turn connects to many target
  ||| components.
  |||
  ||| @dWidth The width of the data bus must be one of [32,16,8].
  ||| @noTargets The number of targets we connect to.
  APB_Initiator_Gen : (dWidth,aWidth,noTargets : Nat)
                   -> (prfD  : ValidArraySpec dWidth [32,16,8])
                   -> (prfA  : ValidArraySpec aWidth [32,16,8])
                   -> (prfT  : IsSucc noTargets)
                   -> IDL APBRTy
  APB_Initiator_Gen dWidth aWidth noTargets prfD prfA prfT = do
    setVendor "ARM"
    setLibrary "examples"
    setName ("APB_Initiator_" <+> show noTargets <+> "_Targets")
    setVersion "0.1"
    setCommunicationStyle Unicast

    c   <- label CLOCK
    r   <- label RESET
    a   <- label ADDR
    p   <- label PROT
    sel <- label SELECT
    e   <- label ENABLE
    w   <- label WRITE
    wd  <- label WDATA
    str <- label STROBE
    rdy <- label READY
    rd  <- label RDATA
    err <- label ERROR

    let dWidth' = fromNat dWidth prfD
    let aWidth' = fromNat aWidth prfA

    clock c Nothing Nothing Nothing
      # system "SYS"
      # fromTargetAlways
    reset r
      # system "SYS"
      # fromTargetAlways
      # setSensitivity Low

    address a aWidth'
    info p (fromNat 2)
    replicate noTargets (control sel)
    control e
    control w
    bus wd dWidth'

    let nrStr = assert_total (div dWidth 8)
    -- nat division is not total.

    replicate nrStr (control str)

    control rdy    # fromTarget
    bus rd dWidth' # fromTarget
    control err    # fromTarget
    stop

  ||| Transform the specification into a model.
  APB_Initiator : (dWidth, aWidth, nrTargets : Nat)
               -> {auto prfD  : ValidArraySpec dWidth [32,16,8]}
               -> {auto prfA  : ValidArraySpec aWidth [32,16,8]}
               -> {auto prfT : IsSucc nrTargets}
               -> InterfaceTy () APBRTy
  APB_Initiator d a t {prfD} {prfA} {prfT} =
    buildSpec (APB_Initiator_Gen d a t prfD prfA prfT)

namespace Target
  ||| This function represents the abstract interface description for
  ||| APBs targeted interface.
  |||
  ||| This interface connect is designed to be connected from a single
  ||| interconnect component, which in turn will connect to a single
  ||| target component.
  |||
  ||| @dWidth The width of the data bus must be one of [32,16,8].
  ||| @aWidth The width of the address bus must be one of [32,16,8].
  APB_Target_Gen : (dWidth,aWidth : Nat)
                -> (prfD  : ValidArraySpec dWidth [32,16,8])
                -> (prfA  : ValidArraySpec aWidth [32,16,8])
                -> IDL APBRTy
  APB_Target_Gen dWidth aWidth prfD prfA = do
    setVendor "ARM"
    setLibrary "examples"
    setName ("APB_Target")
    setVersion "0.1"
    setCommunicationStyle Unicast

    c   <- label CLOCK
    r   <- label RESET
    a   <- label ADDR
    p   <- label PROT
    sel <- label SELECT
    e   <- label ENABLE
    w   <- label WRITE
    wd  <- label WDATA
    str <- label STROBE
    rdy <- label READY
    rd  <- label RDATA
    err <- label ERROR

    let dWidth' = fromNat dWidth prfD
    let aWidth' = fromNat aWidth prfA

    clock c Nothing Nothing Nothing
      # system "SYS"
      # fromTargetAlways
    reset r
      # system "SYS"
      # fromTargetAlways
      # setSensitivity Low

    address a aWidth'
    info p (fromNat 2)

    control sel

    control e
    control w
    bus wd dWidth'

    let nrStr = assert_total (div dWidth 8)
    -- nat division is not total.

    replicate nrStr (control str)

    control rdy    # fromTarget
    bus rd dWidth' # fromTarget
    control err    # fromTarget
    stop

  ||| Transform the specification into a model.
  APB_Target : (dWidth, aWidth : Nat)
            -> {auto prfD  : ValidArraySpec dWidth [32,16,8]}
            -> {auto prfA  : ValidArraySpec aWidth [32,16,8]}
            -> InterfaceTy () APBRTy
  APB_Target d a {prfD} {prfA} =
    buildSpec (APB_Target_Gen d a prfD prfA)
