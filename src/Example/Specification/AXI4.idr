||| This module presents a realisation of ARMs AXI4 protocol using our
||| abstract interface definition language.
module Example.Specification.AXI4

import Data.List
import Data.Vect
import Data.Ranged

import Text.Markup.Edda
import Text.Markup.Edda.Org

import Cordial.EDSL.Specification

%access public export
%default partial

data AXI =
  -- system signals
    ACLK
  | ARESETN
  | ACLKEN

  -- write address
  | AWID
  | AWADDR
  | AWLEN
  | AWSIZE
  | AWBURST
  | AWLOCK
  | AWCACHE
  | AWPROT
  | AWQOS
  | AWREGION
  | AWVALID
  | AWREADY

  -- read address
  | ARID
  | ARADDR
  | ARLEN
  | ARSIZE
  | ARBURST
  | ARLOCK
  | ARCACHE
  | ARPROT
  | ARQOS
  | ARREGION
  | ARVALID
  | ARREADY

  -- write data
  | WID
  | WLAST
  | WDATA
  | WSTRB
  | WVALID
  | WREADY

  -- read response
  | RID
  | RLAST
  | RDATA
  | RRESP
  | RVALID
  | RREADY

  -- write response
  | BID
  | BRESP
  | BVALID
  | BREADY

  -- low poer
  | CSYSREQ
  | CSYSACK
  | CACTIVE

Eq AXI where
  (==) ACLK     ACLK     = True
  (==) ARESETN  ARESETN  = True
  (==) ACLKEN   ACLKEN   = True
  (==) AWID     AWID     = True
  (==) AWADDR   AWADDR   = True
  (==) AWLEN    AWLEN    = True
  (==) AWSIZE   AWSIZE   = True
  (==) AWBURST  AWBURST  = True
  (==) AWLOCK   AWLOCK   = True
  (==) AWCACHE  AWCACHE  = True
  (==) AWPROT   AWPROT   = True
  (==) AWQOS    AWQOS    = True
  (==) AWREGION AWREGION = True
  (==) AWVALID  AWVALID  = True
  (==) AWREADY  AWREADY  = True
  (==) ARID     ARID     = True
  (==) ARADDR   ARADDR   = True
  (==) ARLEN    ARLEN    = True
  (==) ARSIZE   ARSIZE   = True
  (==) ARBURST  ARBURST  = True
  (==) ARLOCK   ARLOCK   = True
  (==) ARCACHE  ARCACHE  = True
  (==) ARPROT   ARPROT   = True
  (==) ARQOS    ARQOS    = True
  (==) ARREGION ARREGION = True
  (==) ARVALID  ARVALID  = True
  (==) ARREADY  ARREADY  = True
  (==) WID      WID      = True
  (==) WLAST    WLAST    = True
  (==) WDATA    WDATA    = True
  (==) WSTRB    WSTRB    = True
  (==) WVALID   WVALID   = True
  (==) WREADY   WREADY   = True
  (==) RID      RID      = True
  (==) RLAST    RLAST    = True
  (==) RDATA    RDATA    = True
  (==) RRESP    RRESP    = True
  (==) RVALID   RVALID   = True
  (==) RREADY   RREADY   = True
  (==) BID      BID      = True
  (==) BRESP    BRESP    = True
  (==) BVALID   BVALID   = True
  (==) BREADY   BREADY   = True
  (==) CSYSREQ  CSYSREQ  = True
  (==) CSYSACK  CSYSACK  = True
  (==) CACTIVE  CACTIVE  = True
  (==) _        _        = False


ValidWidths : List Nat
ValidWidths = [8, 16, 32, 64, 128, 256, 512, 1024]

||| Realisation of the AXI4 protocol.
|||
||| @dWidth The width of the data busses.
||| @aWidth The width of the address busses.
AXI4_Gen : (dWidth, aWidth : Nat)
        -> (prfD : ValidArraySpec dWidth ValidWidths)
        -> (prfA : ValidArraySpec aWidth ValidWidths)
        -> IDL AXI
AXI4_Gen dWidth aWidth prfD prfA = do
  setVendor "ambda.com"
  setLibrary "examples"
  setVersion "r2p0_0"
  setName "AXI4"

  ---------------------
  -- [ Global Signals ]
  ---------------------

  aclk <- label ACLK
  aresetn <- label ARESETN

  clock aclk Nothing Nothing Nothing
    # system "sys"
    # fromTargetAlways
    # opt

  reset aresetn
    # opt
    # fromTargetAlways
    # setSensitivity Low


  --------------------
  -- [ write address ]
  --------------------

  awid <- label AWID
  awaddr <- label AWADDR
  awlen <- label AWLEN
  awsize <- label AWSIZE
  awburst <- label AWBURST
  awlock <- label AWLOCK
  awcache <- label AWCACHE
  awprot <- label AWPROT
  awvalid <- label AWVALID
  awready <- label AWREADY

  control awid  # opt
  address awaddr (fromNat aWidth prfA)

  info awlen   (fromNat 8) # initiatorOpt
  info awsize  (fromNat 3) # initiatorOpt
  info awburst (fromNat 2) # initiatorOpt

  control awlock # opt

  info awcache (fromNat 4) # opt

  info awprot (fromNat 3) # targetOpt

  control awvalid

  control awready # fromTarget

  -----------------
  -- [ write data ]
  -----------------

  wid <- label WID
  wlast <- label WLAST
  wdata <- label WDATA
  wstrb <- label WSTRB
  wvalid <- label WVALID
  wready <- label WREADY

  info wid # opt

  bus wdata (fromNat dWidth prfD)

  let strN = assert_total $ div dWidth (the Nat 8)
  replicate strN (control wstrb)

  control wlast
  control wvalid
  control wready # fromTarget

  ---------------------
  -- [ Write Response ]
  ---------------------

  bid <- label BID
  bresp <- label BRESP
  bvalid <- label BVALID
  bready <- label BREADY

  info bid               # fromTarget  # opt
  info bresp (fromNat 2) # fromTarget
  control bvalid         # fromTarget

  control bready

  ---------------------------
  -- [ read address signals ]
  ---------------------------

  arid <- label ARID
  araddr <- label ARADDR
  arlen <- label ARLEN
  arsize <- label ARSIZE
  arburst <- label ARBURST
  arlock <- label ARLOCK
  arcache <- label ARCACHE
  arprot <- label ARPROT
  arvalid <- label ARVALID
  arready <- label ARREADY

  info arid # opt

  address araddr (fromNat aWidth prfA)

  info arlen   (fromNat 4)
  info arsize  (fromNat 3)
  info arburst (fromNat 2)

  info arlock  (fromNat 2) # opt
  info arcache (fromNat 4) # opt
  info arprot  (fromNat 3) # opt

  control arvalid
  control arready # fromTarget

  ----------------
  -- [ Read Data ]
  ----------------

  rid <- label RID
  rdata <- label RDATA
  rresp <- label RRESP
  rlast <- label RLAST
  rvalid <- label RVALID
  rready <- label RREADY

  info rid                        # fromTarget # opt
  bus rdata (fromNat dWidth prfD) # fromTarget
  info rresp (fromNat 2)          # fromTarget
  control rlast                   # fromTarget
  control rvalid                  # fromTarget
  control rready                  # fromTarget

  --------------------------
  -- [ Low Power Interface ]
  --------------------------

  creq <- label CSYSREQ
  cack <- label CSYSACK
  cact <- label CACTIVE

  control creq # opt # system "clock controller"
  control cack # opt # system "peripheral"
  control cact # opt # system "peripheral"

  stop


||| Realisation of the AXI4 protocol as an initiating interface..
|||
||| @dWidth The width of the data busses.
||| @aWidth The width of the address busses.
AXI4 : (dWidth, aWidth : Nat)
    -> {auto prfD : ValidArraySpec dWidth ValidWidths}
    -> {auto prfA : ValidArraySpec aWidth ValidWidths}
    -> InterfaceTy () AXI
AXI4 d a {prfD} {prfA} =
  buildSpec (AXI4_Gen d a prfD prfA)
