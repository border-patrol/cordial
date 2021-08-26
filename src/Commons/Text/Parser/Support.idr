module Commons.Text.Parser.Support

import Text.Lexer
import Text.Parser

%default total
%access public export

Rule : Type -> Type -> Type
Rule tok ty = Grammar (TokenData tok) True ty


RuleEmpty : Type -> Type -> Type
RuleEmpty tok ty = Grammar (TokenData tok) False ty

export
eoi : (isEOI : a -> Bool) -> RuleEmpty a ()
eoi isEOI = do
    nextIs (isEOI . tok)
    pure ()

export
terminalF : String
         -> (TokenData tok -> Maybe a)
         -> Rule tok a
terminalF x f = terminal f <|> fail x

export
help : Rule tok ty
    -> String
    -> Rule tok ty
help p msg = p <|> fail msg

infixl 0 <?>

export
(<?>) : Rule tok ty
     -> String
     -> Rule tok ty
(<?>) p msg = help p msg

export
match : Eq tok
      => String
      -> a
      -> tok
      -> Rule tok a
match msg v exp =
  terminalF msg
            (\x => if (TokenData.tok x) == exp then Just v else Nothing)
