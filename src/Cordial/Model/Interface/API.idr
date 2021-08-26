module Cordial.Model.Interface.API

import Data.Vect
import Data.DList
import Commons.Data.Ranged

import Text.Markup.Edda

import Cordial.Model.Common
import Cordial.Model.Specification
import Cordial.Model.Projection

import Cordial.Model.Interface.Kinds
import Cordial.Model.Interface.Ports
import Cordial.Model.Interface.PortGroup


%default total
%access public export

(#) : Port annot labelTy endpoint endian type
   -> (Port annot labelTy endpoint endian type
    -> Port annot labelTy endpoint endian type')
   -> Port annot labelTy endpoint endian type'
(#) a f = f a


clock : (info : annot)
     -> (direction : Direction dty endpoint flow prf)
     -> (clockInfo : ClockInfo (Clock mce md mtc) direction)
     -> Port annot labelTy required endpoint endian
             (PortDesc  info' WIRE NoName (Clock mce md mtc) flow      One High opt      IP vorigin doc)
             (PPortDesc       WIRE NoName (Clock mce md mtc) direction One High required IP vorigin)
clock i d = Clock i Empty IP One NoName d High


reset : (info : annot)
     -> (direction : Direction dty endpoint flow prf)
     -> Port annot labelTy required endpoint endian
             (PortDesc  info' WIRE NoName Reset flow      One High opt      IP vorigin doc)
             (PPortDesc       WIRE NoName Reset direction One High required IP vorigin)
reset i d = Reset i Empty IP One NoName d High


interrupt : (info : annot)
         -> (direction : Direction dty endpoint flow prf)
         -> Port annot labelTy required endpoint endian
                 (PortDesc  info' WIRE NoName Interrupt flow      One High opt      IP vorigin doc )
                 (PPortDesc       WIRE NoName Interrupt direction One High required IP vorigin)
interrupt i d = Interrupt i Empty IP One NoName d High


control : (info : annot)
       -> (direction : Direction dty endpoint flow prf)
       -> Port annot labelTy required endpoint endian
               (PortDesc  info' WIRE NoName Control flow      One High opt      IP vorigin doc )
               (PPortDesc       WIRE NoName Control direction One High required IP vorigin)
control i d = Control i Empty IP One NoName d High

address : (info : annot)
       -> (w         : Whole)
       -> (direction : Direction dty endpoint flow prf)
       -> (dendian   : DataEndian endian)
       -> Port annot labelTy required endpoint endian
               (PortDesc  info' ARRAY NoName AddressWire flow      dwidth High opt      IP vorigin doc )
               (PPortDesc       ARRAY NoName AddressWire direction dwidth High required IP vorigin)
address i w d e {dwidth} = Address i Empty IP High NoName (fromWhole w dwidth) d e

bus : (info : annot)
   -> (w         : Whole)
   -> (direction : Direction dty endpoint flow prf)
   -> (dendian   : DataEndian endian)
   -> Port annot labelTy required endpoint endian
           (PortDesc  info' ARRAY NoName DataWire flow      dwidth High opt      IP vorigin doc )
           (PPortDesc       ARRAY NoName DataWire direction dwidth High required IP vorigin)
bus i w d e {dwidth} = Data i Empty IP High NoName (fromWhole w dwidth) d e

general : (info : annot)
       -> (width     : Whole)
       -> (direction : Direction dty endpoint flow prf)
       -> (dendian   : DataEndian endian)
       -> Port annot labelTy required endpoint endian
               (PortDesc  info' wty NoName General flow      dwidth High opt      IP vorigin doc )
               (PPortDesc wty NoName General direction dwidth High required IP vorigin)

general i w d e {dwidth} = General i Empty IP High NoName (fromWhole w dwidth) d e

info : (info      : annot)
    -> (width     : Whole)
    -> (direction : Direction dty endpoint flow prf)
    -> (dendian   : DataEndian endian)
    -> Port annot labelTy required endpoint endian
            (PortDesc  info' wty NoName Information flow      dwidth High opt      IP vorigin doc )
            (PPortDesc       wty NoName Information direction dwidth High required IP vorigin)
info i w d e {dwidth} = Information i Empty IP High NoName (fromWhole w dwidth) d e

namespace Modifier

  setSensitivity : (s : Sensitivity)
                -> Port annot labelTy req endpoint endian
                     (PortDesc  i' w l ty f dw s' opt origin vorigin doc )
                     (PPortDesc    w l ty d dw s' req origin vorigin)
                -> Port annot labelTy req endpoint endian
                   (PortDesc  i' w l ty f dw s opt origin vorigin doc )
                   (PPortDesc    w l ty d dw s req origin vorigin)
  setSensitivity s (General i doc origin s' l width d dendian)     = (General i doc origin s l width d dendian)
  setSensitivity s (Information i doc origin s' l width d dendian) = (Information i doc origin s l width d dendian)
  setSensitivity s (Clock i doc origin width l d s' clockInfo)     = (Clock i doc origin width l d s clockInfo)
  setSensitivity s (Address i doc origin s' l width d dendian)     = (Address i doc origin s l width d dendian)
  setSensitivity s (Data i doc origin s' l width d dendian)        = (Data i doc origin s l width d dendian)
  setSensitivity s (Reset i doc origin size l d s')                = (Reset i doc origin size l d s)
  setSensitivity s (Interrupt i doc origin size l d s')            = (Interrupt i doc origin size l d s)
  setSensitivity s (Control i doc origin size l d s')              = (Control i doc origin size l d s)

  isSystem : (src : String)
          -> Port annot labelTy req endpoint endian
               (PortDesc  i w l ty f dw s opt origin vorigin doc )
               (PPortDesc   w l ty d dw s req origin vorigin)
          -> Port annot labelTy req endpoint endian
               (PortDesc  i w l ty f dw s opt (SYSTEM src) vorigin doc )
               (PPortDesc   w l ty d dw s req (SYSTEM src) vorigin)

  isSystem src (Clock i doc o width label direction sensitivity clockInfo)    = (Clock i doc (SYSTEM src) width label direction sensitivity clockInfo)
  isSystem src (Address i doc o label direction sensitivity size dendian)     = (Address i doc (SYSTEM src) label direction sensitivity size dendian)
  isSystem src (Data i doc o label direction sensitivity size dendian)        = (Data i doc (SYSTEM src) label direction sensitivity size dendian)
  isSystem src (Reset i doc o size label direction sensitivity)               = (Reset i doc (SYSTEM src) size label direction sensitivity)
  isSystem src (Interrupt i doc o size label direction sensitivity)           = (Interrupt i doc (SYSTEM src) size label direction sensitivity)
  isSystem src (Control i doc o size label direction sensitivity)             = (Control i doc (SYSTEM src) size label direction sensitivity)
  isSystem src (General i doc o label direction sensitivity size dendian)     = (General i doc (SYSTEM src) label direction sensitivity size dendian)
  isSystem src (Information i doc o label direction sensitivity size dendian) = (Information i doc (SYSTEM src) label direction sensitivity size dendian)

  namespace PortGroup
    isSystem : (src : String)
             -> PortGroup annot labelTy endpoint endian ps pps
             -> PortGroup annot labelTy endpoint endian (map (\p => record {origin = (SYSTEM src)} p) ps) (setOrigin (SYSTEM src) pps)
    isSystem src xs with (xs)
      isSystem src xs | Empty           = Empty
      isSystem src xs | (Add port rest) = Add (isSystem src port) (isSystem src rest)
      isSystem src xs | (Skip rest)     = Skip (isSystem src rest)

  addDoc : (src : String)
        -> (p   : String -> Either String (Edda SNIPPET))
        -> Port annot labelTy req endpoint endian
                (PortDesc  i w label ty f dw s opt origin vorigin doc )
                (PPortDesc   w label ty d dw s req origin vorigin)
        -> Port annot labelTy req endpoint endian
                (PortDesc  i w label ty f dw s opt origin vorigin doc )
                (PPortDesc   w label ty d dw s req origin vorigin)
  addDoc src p (Clock i doc o width label direction sensitivity clockInfo)    = (Clock i (newDocString src p)  o width label direction sensitivity clockInfo)
  addDoc src p (Address i doc o label direction sensitivity size dendian)     = (Address i (newDocString src p)  o label direction sensitivity size dendian)
  addDoc src p (Data i doc o label direction sensitivity size dendian)        = (Data i (newDocString src p)  o label direction sensitivity size dendian)
  addDoc src p (Reset i doc o size label direction sensitivity)               = (Reset i (newDocString src p)  o size label direction sensitivity)
  addDoc src p (Interrupt i doc o size label direction sensitivity)           = (Interrupt i (newDocString src p)   o size label direction sensitivity)
  addDoc src p (Control i doc o size label direction sensitivity)             = (Control i (newDocString src p)   o size label direction sensitivity)
  addDoc src p (General i doc o label direction sensitivity size dendian)     = (General i (newDocString src p)  o label direction sensitivity size dendian)
  addDoc src p (Information i doc o label direction sensitivity size dendian) = (Information i (newDocString src p)  o label direction sensitivity size dendian)

  (:=) : (name : Name kind labelTy)
      -> Port annot labelTy req endpoint endian
              (PortDesc  i w l ty f dw s opt origin vorigin doc )
              (PPortDesc   w l ty d dw s req origin vorigin)
      -> Port annot labelTy req endpoint endian
              (PortDesc  i w name ty f dw s opt origin vorigin doc )
              (PPortDesc   w name ty d dw s req origin vorigin)
  (:=) label (General     i doc origin s l width d dendian)   = (General     i doc origin s label width d dendian)
  (:=) label (Information i doc origin s l width d dendian)   = (Information i doc origin s label width d dendian)
  (:=) label (Clock       i doc origin width l d s clockInfo) = (Clock       i doc origin width label d s clockInfo)
  (:=) label (Address     i doc origin s l width d dendian)   = (Address     i doc origin s label width d dendian)
  (:=) label (Data        i doc origin s l width d dendian)   = (Data        i doc origin s label width d dendian)
  (:=) label (Reset       i doc origin size l d s)            = (Reset       i doc origin size label d s)
  (:=) label (Interrupt   i doc origin size l d s)            = (Interrupt   i doc origin size label d s)
  (:=) label (Control     i doc origin size l d s)            = (Control     i doc origin size label d s)



-- --------------------------------------------------------------------- [ EOF ]
