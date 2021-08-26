||| Module    : Action.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
||| In some cases `Maybe` is not sufficient to describe the results of
||| operations. Here we describe a more Generic result data type.
module Commons.Data.Action

%access public export

||| Operations either return a success or some result, we use
||| `ActionTy` to differentiate between the two.
data ActionTy = SUCCESS | RESULT

||| A custom return type for operations.
|||
||| @aty What type of action are we performing.
||| @rty The return type for an action that returns a value.
||| @ety The error type for an action.
|||
data Action : (aty : ActionTy)
           -> (ety : Type)
           -> (rty : Type)
           -> Type
  where
    ||| The operation completed successfully and doesn't return a
    ||| result.
    Success : Action SUCCESS ety rty

    ||| The operation returns a result of type `rty`.
    |||
    ||| @rty The value returned.
    Result : rty -> Action RESULT ety rty

    ||| The operation failed and the given error was produced.
    |||
    ||| @ety The reported error.
    Error : ety -> Action aty ety rty

||| Given an `action` if it was successful return `success` otherwise return `backup`.
success : (backup  : Lazy b)
       -> (success : Lazy b)
       -> (action  : Action SUCCESS ety rty)
       -> b
success _      success Success   = success
success backup _       (Error x) = backup

||| Given an `action` if it was successful apply `transform` otherwise return `backup`.
result : (backup     : Lazy b)
      -> (transform  : Lazy (rty -> b))
      -> (result : Action RESULT ety rty)
      -> b
result _      transform (Result x) = transform x
result backup _         (Error x)  = backup

runEitherIO : IO (Either ety rty) -> IO $ Action RESULT ety rty
runEitherIO func =
  case !func of
    Left err  => pure $ Error  err
    Right res => pure $ Result res

(Show rty, Show ety) => Show (Action ty ety rty) where
  show Success    = "Success"
  show (Result x) = unwords ["Result", show x]
  show (Error  x) = unwords ["Error", show x]

(Eq rty, Eq ety) => Eq (Action aty ety rty) where
  (==) Success    Success    = True
  (==) (Result x) (Result y) = x == y
  (==) (Error x)  (Error y)  = x == y
  (==) _          _          = False

export
Functor (Action aty ety) where
    map f (Error l)  = Error l
    map f Success    = Success
    map f (Result r) = Result (f r)

export
Applicative (Action RESULT ety) where
  pure = Result

  (<*>) (Result f)  (Result x)  = Result (f x)
  (<*>) (Result _)  (Error err) = Error err
  (<*>) (Error err) _           = Error err

combine : Action SUCCESS eTy ()
       -> Action SUCCESS eTy ()
       -> Action SUCCESS eTy ()
combine Success     Success     = Success
combine Success     (Error err) = Error err
combine (Error err) _           = Error err

export
Monad (Action RESULT ety) where
  (>>=) (Result x) f = f x
  (>>=) (Error x)  f = Error x


-- --------------------------------------------------------------------- [ EOF ]
