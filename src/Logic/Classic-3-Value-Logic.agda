{-# OPTIONS --without-K --exact-split --safe #-}

module Logic.Classic-3-Value-Logic where

open import TypeTheory.Universes
open import TypeTheory.SimpleTypes

-- 3 element type
-- Kleene and Priest logics
data Three : Type 𝑢0 where
  yes : Three
  perhaps : Three
  no : Three

-- Induction principle
Three-induction : (P : Three -> Type 𝑢)
   -> P yes
   -> P perhaps
   -> P no
   -> (t : Three) -> P t  -- property P holds for all element of Three
Three-induction P py pp pn yes     = py
Three-induction P py pp pn perhaps = pp
Three-induction P py pp pn no      = pn

-- TODO Three-recursion
-- TODO Three-iteration

not3_ : Three -> Three
not3 yes     = no
not3 perhaps = perhaps
not3 no      = yes

_&&3_ : Three -> Three -> Three
no      &&3 y  = no
yes     &&3 no = no
perhaps &&3 no = no
yes &&3 yes = yes
yes &&3 perhaps     = perhaps
perhaps &&3 yes     = perhaps
perhaps &&3 perhaps = perhaps

_||3_ : Three -> Three -> Three
yes     ||3 y   = yes
perhaps ||3 yes = yes
no      ||3 yes = yes

no ||3 no = no

perhaps ||3 perhaps = perhaps
perhaps ||3 no      = perhaps
no      ||3 perhaps = perhaps

-- TODO https://en.wikipedia.org/wiki/Three-valued_logic
