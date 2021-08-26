-- ----------------------------------------------------------- [ SimpleDot.idr ]
-- Module    : SimpleDot.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

||| A Simple Graph representation for Dot.
module Commons.Data.Graphviz.SimpleDot

import Data.AVL.Graph

%access export

-- ------------------------------------------------------------------- [ Utils ]

toKVString : List (String, String) -> List String
toKVString Nil         = Nil
toKVString ((x,y)::xs) = (x ++ "=" ++ show y) :: toKVString xs

compact : List String -> String
compact Nil = ""
compact (x::xs) = x ++ compact xs

showAttrs : List (String, String) -> String
showAttrs Nil = ";"
showAttrs xs  = unwords
    [ "["
    , compact $ intersperse "," (toKVString xs)
    , "];"]


-- -------------------------------------------------------------------- [ ADTs ]

public export
data SDTy = NODE | GRAPH | EDGE

||| A simple dot file with no sub-graphs.
public export
data SimpleDot : SDTy -> Type where
  Node    : NodeID -> List (String, String)                -> SimpleDot NODE
  Edge    : NodeID -> NodeID -> List (String, String)      -> SimpleDot EDGE
  Digraph : List (SimpleDot NODE) -> List (SimpleDot EDGE) -> SimpleDot GRAPH
  Graph   : List (SimpleDot NODE) -> List (SimpleDot EDGE) -> SimpleDot GRAPH

-- -------------------------------------------------------------------- [ Show ]

Show (SimpleDot x) where
  show (Node i as) = unwords [ show i, showAttrs as]
  show (Edge x y as) = unwords
      [ show x
      , "->"
      , show y
      , showAttrs as
      ]
  show (Digraph ns es) = unlines ["digraph g ", unlines ["{" , unlines $ map show ns, "\n\n", unlines $ map show es, "}\n"]]
  show (Graph   ns es) = unlines [show "graph g ", unlines ["{" , unlines $ map show ns, "\n\n", unlines $ map show es, "}\n"]]

-- --------------------------------------------------------------- [ Transform ]

||| Convert a Graph to a simple dot node.
|||
||| @mkNodeLabel How to make a node label.
||| @mkEdgeLabel How to make a edge label.
toDot : Graph v e
     -> (mkNodeLabel : v -> String)
     -> (mkEdgeLabel : Edge e -> SimpleDot EDGE)
     -> SimpleDot GRAPH
toDot g mkNodeLabel mkEdgeLabel = Digraph ns es
  where
    getNodeLabel : NodeID -> String
    getNodeLabel n = case getValueByID n g of
        Nothing => ""
        Just u  => mkNodeLabel u

    ns : List (SimpleDot NODE)
    ns = map (\x => Node x [("label", getNodeLabel x)]) (verticesID g)

    es : List (SimpleDot EDGE)
    es = map mkEdgeLabel (edges g)

-- --------------------------------------------------------------------- [ EOF ]
