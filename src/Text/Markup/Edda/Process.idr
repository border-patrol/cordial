module Text.Markup.Edda.Process

import Data.AVL.Dict

import Text.Markup.Edda.Model.Common
import Text.Markup.Edda.Model.Raw
import Text.Markup.Edda.Model.Processed

import Text.Markup.Edda.Process.Inline
import Text.Markup.Edda.Process.Block

%default total
%access export

export
processDoc : EddaRaw DOC -> Edda DOC
processDoc (Doc title attrs body) = Doc (process title) attrs (process body)

export
processSnippet : EddaRaw SNIPPET -> Edda SNIPPET
processSnippet (Snippet content prf) with (prf)
  processSnippet (Snippet content prf) | IsInLine = Snippet (process content) prf
  processSnippet (Snippet content prf) | IsBlock = Snippet (process content) prf
