-- ----------------------------------------------------------------- [ Org.idr ]
-- Module    : Org.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
module Text.Markup.Edda.Test.Org

import Text.Markup.Edda.Model
import Text.Markup.Edda.Reader.Org

import Lightyear.Testing

export
runTests : IO ()
runTests = Testing.runTests [
      parseTest ( "Markup") (many $ lexeme inline) "asasas *bold* /italic/ ~code~ +strike-through+ =verbatim= $mart$ Hello 'Bye bye'.\n"

    , parseTest ( "Links 1") (many inline) "[[http://www.cs.st-andrews.ac.uk][URL]] [[http://www.cs.st-andrews.ac.uk][URL]] [[http://www.cs.st-andrews.ac.uk][URL]]\n"

    , parseTest ( "Links 2") (many inline) "[[http://www.cs.st-andrews.ac.uk]] [[Boneh2001]] [[citet:Boneh2001]] [[citep:Boneh2001]]\n"

    , parseTest ( "Links 3") (many inline) "[fn:label:description]\n"

    , parseTest ("Attribute Title")  (attribute "TITLE")  "#+TITLE: I am a Title\n\n"
    , parseTest ("Attribute Author") (attribute "AUTHOR") "#+AUTHOR: I am an Author\n\n"
    , parseTest ("Attribute Date ")  (attribute "DATE")   "#+DATE: I is a date\n\n"

    , parseTest ( "Environments")
                (many block)
                """#+CAPTION: sdsd
#+NAME: asas:asasre
#+BEGIN_THEOREM
sdsdsdsd
#+END_THEOREM
#+CAPTION: sdsd
#+NAME: asas:asasre
#+BEGIN_COROLLARY
sdsdsdsd
#+END_COROLLARY
#+CAPTION: sdsd
#+NAME: asas:asasre
#+BEGIN_LEMMA
sdsdsdsd
#+END_LEMMA
#+CAPTION: sdsd
#+NAME: asas:asasre
#+BEGIN_PROPOSITION
sdsdsdsd
#+END_PROPOSITION
#+CAPTION: sdsd
#+NAME: asas:asasre
#+BEGIN_PROOF
sdsdsdsd
#+END_PROOF
#+CAPTION: sdsd
#+NAME: asas:asasre
#+BEGIN_DEFINITION
sdsdsdsd
#+END_DEFINITION
#+CAPTION: sdsd
#+NAME: asas:asasre
#+BEGIN_EXAMPLE
sdsdsdsd
#+END_EXAMPLE
#+CAPTION: sdsd
#+NAME: asas:asasre
#+BEGIN_EXERCISE
sdsdsdsd
#+END_EXERCISE
#+CAPTION: sdsd
#+NAME: asas:asasre
#+BEGIN_NOTE
sdsdsdsd
#+END_NOTE
#+CAPTION: sdsd
#+NAME: asas:asasre
#+BEGIN_PROBLEM
sdsdsdsd
#+END_PROBLEM
#+CAPTION: sdsd
#+NAME: asas:asasre
#+BEGIN_QUESTION
sdsdsdsd
#+END_QUESTION
#+CAPTION: sdsd
#+NAME: asas:asasre
#+BEGIN_REMARK
sdsdsdsd
#+END_REMARK
#+CAPTION: sdsd
#+NAME: asas:asasre
#+BEGIN_SOLUTION
sdsdsdsd
#+END_SOLUTION
"""

    , parseTest ( "Headers")
                (many header)
                """* Introduction

** Contribution

** Outline

* Methodology

** System

** Procedure

* Results

* Discussion

* Conclusion

"""

    , parseTest ( "Source Block 1")
                (orgBlock)
                """#+CAPTION: sdsd
#+NAME: asas:asasre
#+BEGIN_SRC idris

main : IO ()
main = putStrLn "Hello World!"
#+END_SRC

"""

    , parseTest ( "Source Block 2")
                (orgBlock)
                """#+BEGIN_SRC idris
main : IO ()
main = putStrLn "Hello World!"
main : IO ()
main = putStrLn "Hello World!"
#+END_SRC

"""

    , parseTest ( "Quotes")
                (orgBlock)
                """#+BEGIN_QUOTE
dfkljfzdjf
#+END_QUOTE

"""

    , parseTest ( "Figures")
           (orgBlock)
           """#+CAPTION: sdsd
#+NAME: asas:asasre
[[dfjkdjfldjkf]]

"""

    , parseTest ( "Equations")
                (many orgBlock)
                """#+BEGIN_EQUATION
y = a*x^2 + b*x + c
#+END_EQUATION

#+NAME: asas
#+BEGIN_EQUATION
y^2 = x^3 + ax + b
#+END_EQUATION

"""

    , parseTest ("Lists")
                (many orgBlock)
                """+ a
+ b
+ c
+ a
+ b
+ c
- a
- b
- c


1. a
1. b
2. c
3. a
3. b
1. c
2. a
2. b
3. c


+ Term :: Description
+ Term :: Description
+ Term :: Description
+ Term :: Description
+ Term :: Description
+ Term :: Description


"""
    ]
-- --------------------------------------------------------------------- [ EOF ]
