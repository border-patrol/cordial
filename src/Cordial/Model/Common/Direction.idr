module Cordial.Model.Common.Direction

import Cordial.Model.Common.Essential

%access public export
%default total

||| How information flows through the channel.
data Flow : Type where
  PC     : Flow -- Producer to Consumer
  CP     : Flow -- Consumer to Producer
  PCCP   : Flow -- Bi Directional
  ConstP : Flow -- Always producer
  ConstC : Flow -- Always consume

data DirectionTy = IsIn | IsOut | IsInOut

data DirectionKind : Endpoint -> Flow -> DirectionTy -> Type where
    InPC  : DirectionKind CONSUMER PC IsIn
    OutPC : DirectionKind PRODUCER PC IsOut

    InCP  : DirectionKind PRODUCER CP IsIn
    OutCP : DirectionKind CONSUMER CP IsOut

    InOut : DirectionKind pccp PCCP IsInOut

    OutConstP : DirectionKind p ConstP IsOut
    InConstC  : DirectionKind c ConstC IsIn

%hint
calcDirTy : Endpoint -> Flow -> DirectionTy
calcDirTy PRODUCER PC     = IsOut
calcDirTy CONSUMER PC     = IsIn
calcDirTy PRODUCER CP     = IsIn
calcDirTy CONSUMER CP     = IsOut
calcDirTy y        PCCP   = IsInOut
calcDirTy y        ConstP = IsOut
calcDirTy y        ConstC = IsIn

%hint
calcDirKind : (endpoint : Endpoint)
           -> (flow     : Flow)
           -> DirectionKind endpoint flow (calcDirTy endpoint flow)
calcDirKind e f with (e)
  calcDirKind e f | PRODUCER with (f)
    calcDirKind e f | PRODUCER | PC = OutPC
    calcDirKind e f | PRODUCER | CP = InCP
    calcDirKind e f | PRODUCER | PCCP = InOut
    calcDirKind e f | PRODUCER | ConstP = OutConstP
    calcDirKind e f | PRODUCER | ConstC = InConstC

  calcDirKind e f | CONSUMER with (f)
    calcDirKind e f | CONSUMER | PC = InPC
    calcDirKind e f | CONSUMER | CP = OutCP
    calcDirKind e f | CONSUMER | PCCP = InOut
    calcDirKind e f | CONSUMER | ConstP = OutConstP
    calcDirKind e f | CONSUMER | ConstC = InConstC


||| The 'actual' direction of information flow through an interface
data Direction : (ty : DirectionTy)
              -> (endpoint : Endpoint)
              -> (flow : Flow)
              -> (prf  : DirectionKind endpoint flow ty)
              -> Type
  where
    IN    : Direction IsIn    endpoint flow kind
    OUT   : Direction IsOut   endpoint flow kind
    INOUT : Direction IsInOut endpoint flow kind

%hint
calcDirection : (endpoint : Endpoint)
             -> (flow     : Flow)
             -> Direction (calcDirTy endpoint flow) endpoint flow (calcDirKind endpoint flow)
calcDirection endpoint flow with (calcDirKind endpoint flow)
  calcDirection CONSUMER PC | InPC = IN
  calcDirection PRODUCER PC | OutPC = OUT
  calcDirection PRODUCER CP | InCP = IN
  calcDirection CONSUMER CP | OutCP = OUT
  calcDirection endpoint PCCP | InOut = INOUT
  calcDirection endpoint ConstP | OutConstP = OUT
  calcDirection endpoint ConstC | InConstC = IN

namespace Calculated
     Direction : (endpoint : Endpoint)
              -> (flow : Flow)
              -> Type
     Direction endpoint flow = Direction.Direction (calcDirTy endpoint flow) endpoint flow (calcDirKind endpoint flow)
-- --------------------------------------------------------------------- [ EOF ]
