||| This module presents the Xilinx LocalLink protocol encoded within
||| out abstract interfact description language.
module Example.Specification.LocalLink

import Text.Markup.Edda
import Text.Markup.Edda.Org

import Cordial.EDSL.Specification

%access public export
%default total

||| Concrete labels for port descriptions.
data LLRTy = CLOCK | RESET | DATA | SRC_RDY | DST_RDY | SOF | EOF
           | SOP | EOP
           | REM | REM_SOF | REM_SOP | REM_EOP
           | SRC_DSC | DST_DSC
           | CH | CH_RDY | CH_SWAP
           | PARITY | PARITY_ERR

||| Equality type is required to differentiate labels.
Eq LLRTy where
  (==) CLOCK      CLOCK      = True
  (==) RESET      RESET      = True
  (==) DATA       DATA       = True
  (==) SRC_RDY    SRC_RDY    = True
  (==) DST_RDY    DST_RDY    = True
  (==) SOF        SOF        = True
  (==) EOF        EOF        = True
  (==) SOP        SOP        = True
  (==) EOP        EOP        = True
  (==) REM        REM        = True
  (==) REM_SOF    REM_SOF    = True
  (==) REM_SOP    REM_SOP    = True
  (==) REM_EOP    REM_EOP    = True
  (==) SRC_DSC    SRC_DSC    = True
  (==) DST_DSC    DST_DSC    = True
  (==) CH         CH         = True
  (==) CH_RDY     CH_RDY     = True
  (==) CH_SWAP    CH_SWAP    = True
  (==) PARITY     PARITY     = True
  (==) PARITY_ERR PARITY_ERR = True
  (==) _          _          = False

||| ENcodes the remainder kind.
data TyRemainder = ENCODED | MASK

||| This function represents the 'generic' specification for the
||| LocalLink protocol.
|||
||| We diverge from the formal specification presented by embracing
||| Cordial's EDSL nature to allow more value dependencies than
||| presented in the paper.
|||
||| *Note* For several busses it is not clear what the width should
||| be. This is a result of calculations resulting in an array of $1 -
||| 1$ length, coupled with loose specification, or widths that
||| require floating point arithemetic.  The latter is something that
||| the formalism does not support natively w.r.t. Widths.
|||
||| We have left those widths 'undefined'.
|||
||| @dWidth The width of the data bus must be one of [32,16,8].
||| @noChans The number of channels supported.
||| @rTy     The kind of remainder.
LocalLink_Gen : (dWidth, noChans : Nat)
             -> (rTy  : TyRemainder)
             -> (prfD : ValidArraySpec dWidth [32,16,8])
             -> (prfC : GTE noChans 1)
             -> IDL LLRTy
LocalLink_Gen dWidth noChans rTy prfD prfC = do
  setVendor "XILINX"
  setLibrary "examples"
  setName ("LocalLink")
  setVersion "0.1"
  setCommunicationStyle Unicast

  c                 <- label CLOCK
  r                 <- label RESET
  d                 <- label DATA
  rdy_src           <- label SRC_RDY
  rdy_dst           <- label DST_RDY
  frame_start       <- label SOF
  frame_end         <- label EOF
  payload_start     <- label SOP
  payload_end       <- label EOP
  rem               <- label REM
  rem_frame_start   <- label REM_SOF
  rem_payload_start <- label REM_SOP
  rem_payload_end   <- label REM_EOP
  disco_src         <- label SRC_DSC
  disco_dst         <- label DST_DSC
  chan              <- label CH
  chan_rdy          <- label CH_RDY
  chan_swp          <- label CH_SWAP
  parity            <- label PARITY
  perr              <- label PARITY_ERR

  clock c Nothing Nothing Nothing
    # fromTargetAlways
    # system "sys"

  reset r
    # fromTargetAlways
    # system "sys"
    # setSensitivity Low

  bus d (fromNat dWidth prfD)
  control rdy_src # setSensitivity Low
  control rdy_dst # setSensitivity Low # fromTarget

  control frame_start # opt # setSensitivity Low
  control frame_end   # opt # setSensitivity Low

  control payload_start # opt
  control payload_end   # opt

  let d_dbl = cast {to=Double} dWidth
  let remsize = case rTy of
      ENCODED => calcBits d_dbl
      MASK    => (d_dbl / 8) - 1

  let p_width = FromDouble.fromDouble remsize

  bus rem               # opt
  bus rem_frame_start   # opt
  bus rem_payload_start # opt
  bus rem_payload_end   # opt
  -- Ideally specify bus with width p_width but no proof that `p_wdith >= 2`

  -- [ NOTE]

  control disco_src              # opt
  control disco_dst # fromTarget # opt

  control perr
    # opt
    # fromTarget
    # setSensitivity Low

  let paritysize = assert_total $ minus (div dWidth 8) 1
  -- nat division is not total

  bus parity # opt
  -- Ideally specify bus with width paritysize but no proof that `paritysize >= 2`

  let csize = calcBits (cast {to=Double} noChans)

  bus chan # opt
    -- Ideally specify bus with width csize but no proof that `csize >= 2`

  bus chan_rdy  # opt # setSensitivity Low
  bus chan_swp  # opt
  -- Ideally specify bus with a bus width of noChans but no proof that `noChans >= 2` must hold.
  stop

||| Transform the specification into a model.
LocalLink : (dWidth, noChans : Nat)
         -> (rTy : TyRemainder)
         -> {auto prfD : ValidArraySpec dWidth [32,16,8]}
         -> {auto prfC : GTE noChans 1}
         -> InterfaceTy () LLRTy
LocalLink d c r {prfD} {prfC} =
  buildSpec (LocalLink_Gen d c r prfD prfC)


-- --------------------------------------------------------------------- [ EOF ]
