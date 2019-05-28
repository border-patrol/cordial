module PrettyPrint.SExpr

%default total
%access private

export
mkSExprStr : Show a => String -> a -> String
mkSExprStr k v = concat ["(", k, " (", show v, "))"]

export
mkSExpr : Show a => String -> a -> String
mkSExpr = mkSExprStr
