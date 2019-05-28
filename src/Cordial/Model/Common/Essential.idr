module Cordial.Model.Common.Essential

%default total
%access public export

infixl 8 #
infixr 6 :=

-- -------------------------------------------------------------- [ Properties ]

data ConnectionTy = BUS | ADHOC

||| With respect to the Comms protocol as a whole, does the IP
||| interface produce or consume signals.
data Endpoint = PRODUCER | CONSUMER

||| Does the bus support broadcasting, or unicast connections.
data CommStyle = Broadcast | Unicast

||| Where does the Port originate from.
data Origin = SYSTEM String | IP

||| For arrays we note the endian value
data Endian = Big | Little

||| Capture wire sensitivity
data Sensitivity = High | Low | Rising | Falling | Insensitive

data Polarity = ActiveHigh | ActiveLow

||| For default signal values
data Value = Zero | One

||| Capture port shape
data PortShape = WIRE | ARRAY

data ClockEdge = Rise | Fall

data Delay = Max Nat | Min Nat

-- --------------------------------------------------------------------- [ EOF ]
