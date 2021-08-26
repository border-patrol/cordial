module Commons.Text.Display

%access public export
%default total

||| Present a version `String` of `a` for display.
|||
||| By default `Display` displays `a`s `Show` instance.
|||
||| Unlike `Show` there is no link to `Read`, and should see this as
||| inbetween `Pretty` and `Show`, that is useful for adhoc `toString`
||| methods.
interface Display a where
  display : a -> String

Display String where
  display x = x

Display Int where
  display x = show x

Display Nat where
  display n = show (the Integer (cast n))

Display Bool where
  display True = "True"
  display False = "False"

-- --------------------------------------------------------------------- [ EOF ]
