-- ------------------------------------------------------------- [ DayTime.idr ]
||| Module    : DayTime.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
module Commons.Data.DayTime

%default total
%access public export

-- ----------------------------------------------------------------- [ DayTime ]
||| Simple Record for DayTime
record DayTime where
  constructor MkDaytime
  year    : Int
  month   : Int
  day     : Int
  hour    : Int
  minute  : Int
  seconds : Int


Show DayTime where
    show date = unwords [show (year    date), "-",
                         show (month   date), "-",
                         show (day     date), " ",
                         show (hour    date), ":",
                         show (minute  date), ":",
                         show (seconds date) ]

-- --------------------------------------------------------------------- [ EOF ]
