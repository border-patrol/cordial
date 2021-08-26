module Commons.Config.JSON.Parser

import Data.PList

import Text.Token
import Text.Lexer
import Text.Parser

import Language.JSON.Lexer

import Commons.Config.JSON.Model
import Commons.Config.JSON.Helpers

%default total
%access private

public export
Parser : Type -> Type
Parser = Grammar JSONToken True

symbol : Punctuation -> Grammar JSONToken True ()
symbol p = match $ JTPunct p


null : Parser ParseResult
null = do
  match JTNull
  pure $ PR VALUE JNull ValidVal

number : Parser ParseResult
number = do
  res <- match JTNumber
  pure $ PR VALUE (JNum res) ValidVal

boolean : Parser ParseResult
boolean = do
  res <- match JTBoolean
  pure $ PR VALUE (JBool res) ValidVal

string' : Parser String
string' = do
  res <- match JTString
  the (Grammar _ False _) $
    case res of
      Just str => pure str
      Nothing  => fail "invalid string"

string : Parser ParseResult
string = do
  res <- match JTString
  the (Grammar _ False _) $
    case res of
      Just str => pure $ PR VALUE (JStr str) ValidVal
      Nothing  => fail "invalid string"


value : Parser ParseResult
value = null <|> string <|> number <|> boolean

mutual
  array : Parser ParseResult
  array = do
      symbol (Square Open)
      commit
      vs <- elements
      symbol (Square Close)
      pure $ PR ARRAY (toArray vs) ValidArr
    where
     elements : Parser (List ParseResult)
     elements = do
       v <- json
       vs <- option Nil $ (symbol Comma) *> sepBy (symbol Comma) json
       pure (v::vs)

  dict : Parser ParseResult
  dict = do
      symbol (Curly Open)
      commit
      kvs <- keypairs
      symbol (Curly Close)
      pure $ PR MAP (toDict kvs) ValidMap
    where
      keypair : Parser (String, ParseResult)
      keypair = do
        key <- string'
        symbol Colon
        value <- json
        pure (key, value)

      keypairs : Parser (List (String, ParseResult))
      keypairs = do
        kp <- keypair
        kps <- option Nil $ (symbol Comma) *> sepBy (symbol Comma) keypair
        pure (kp::kps)

  json : Parser ParseResult
  json = value <|> array <|> dict

export
parseJSON : List JSONToken -> Maybe (JSONDoc DOC)
parseJSON toks =
  case parse json $ filter (not . ignored) toks of
    (Left (Error x xs)) => Nothing
    (Right (a, b)) =>
      case a of
         (PR ty value prf) => Just $ JDoc ty value
