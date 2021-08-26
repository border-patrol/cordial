-- --------------------------------------------------------------- [ Utils.idr ]
-- Module    : Utils.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
module Text.Markup.Edda.Process.Utils

import Data.AVL.Dict

%default total
%access export

lookupType : Dict String String -> Maybe String
lookupType = lookup "type"

lookupSrcLang : Dict String String -> Maybe String
lookupSrcLang = lookup "src_lang"

lookupSrcOpts : Dict String String -> Maybe String
lookupSrcOpts = lookup "src_opts"

nubAttribute : String -> Dict String String -> Dict String String
nubAttribute key as = fromList $ doNub key (toList as)
  where
    doNub : String -> List (String, String) -> List (String, String)
    doNub _   Nil     = Nil
    doNub key ((k,v)::xs) =
      case key == k of
        True => doNub key xs
        False => (k,v) :: doNub key xs

-- --------------------------------------------------------------------- [ EOF ]
