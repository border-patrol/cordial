module Cordial.Model.Common.Necessary

import Cordial.Model.Common.Essential

%access public export
%default total

data OptTy = REQ | OPT

data OptionalTy = CompletelyOptional
                | ProducerOptional
                | ConsumerOptional
                | IsRequired

%hint
calcOptTy : (endpoint : Endpoint)
         -> (optTy    : OptionalTy)
         -> OptTy
calcOptTy PRODUCER CompletelyOptional = OPT
calcOptTy PRODUCER ProducerOptional = OPT
calcOptTy PRODUCER ConsumerOptional = REQ
calcOptTy PRODUCER IsRequired = REQ
calcOptTy CONSUMER CompletelyOptional = OPT
calcOptTy CONSUMER ProducerOptional = REQ
calcOptTy CONSUMER ConsumerOptional = OPT
calcOptTy CONSUMER IsRequired = REQ

data OptionalKind : (endpoint : Endpoint)
                 -> (opt : OptionalTy)
                 -> (ty  : OptTy)
                 -> Type
  where
    IsOptPA : OptionalKind PRODUCER CompletelyOptional OPT
    IsOptPP : OptionalKind PRODUCER ProducerOptional   OPT
    IsReqPC : OptionalKind PRODUCER ConsumerOptional   REQ
    IsReqPR : OptionalKind PRODUCER IsRequired         REQ

    IsOptCA : OptionalKind CONSUMER CompletelyOptional OPT
    IsReqCP : OptionalKind CONSUMER ProducerOptional   REQ
    IsOptCC : OptionalKind CONSUMER ConsumerOptional   OPT
    IsReqCR : OptionalKind CONSUMER IsRequired         REQ

||| Is the port required or optional
data Necessary : (ty : OptTy)
              -> (endpoint : Endpoint)
              -> (optTy : OptionalTy)
              -> (prf : OptionalKind endpoint optTy ty)
              -> Type
  where
   Required : Necessary REQ endpoint opt kind
   Optional : Necessary OPT endpoint opt kind

%hint
calcOptKind : (endpoint : Endpoint)
           -> (opt      : OptionalTy)
           -> OptionalKind endpoint opt (calcOptTy endpoint opt)
calcOptKind endpoint opt with (endpoint)
  calcOptKind endpoint opt | PRODUCER with (opt)
    calcOptKind endpoint opt | PRODUCER | CompletelyOptional = IsOptPA
    calcOptKind endpoint opt | PRODUCER | ProducerOptional = IsOptPP
    calcOptKind endpoint opt | PRODUCER | ConsumerOptional = IsReqPC
    calcOptKind endpoint opt | PRODUCER | IsRequired = IsReqPR

  calcOptKind endpoint opt | CONSUMER with (opt)
    calcOptKind endpoint opt | CONSUMER | CompletelyOptional = IsOptCA
    calcOptKind endpoint opt | CONSUMER | ProducerOptional = IsReqCP
    calcOptKind endpoint opt | CONSUMER | ConsumerOptional = IsOptCC
    calcOptKind endpoint opt | CONSUMER | IsRequired = IsReqCR


%hint
calcNecessary : (endpoint : Endpoint)
             -> (opt      : OptionalTy)
             -> Necessary (calcOptTy endpoint opt) endpoint opt (calcOptKind endpoint opt)
calcNecessary endpoint opt with (calcOptKind endpoint opt)
  calcNecessary PRODUCER CompletelyOptional | IsOptPA = Optional
  calcNecessary PRODUCER ProducerOptional | IsOptPP = Optional
  calcNecessary PRODUCER ConsumerOptional | IsReqPC = Required
  calcNecessary PRODUCER IsRequired | IsReqPR = Required
  calcNecessary CONSUMER CompletelyOptional | IsOptCA = Optional
  calcNecessary CONSUMER ProducerOptional | IsReqCP = Required
  calcNecessary CONSUMER ConsumerOptional | IsOptCC = Optional
  calcNecessary CONSUMER IsRequired | IsReqCR = Required

namespace Calculated
     Necessary : (endpoint : Endpoint)
              -> (opt : OptionalTy)
              -> Type
     Necessary endpoint flow = Necessary.Necessary (calcOptTy endpoint flow) endpoint flow (calcOptKind endpoint flow)
-- --------------------------------------------------------------------- [ EOF ]
