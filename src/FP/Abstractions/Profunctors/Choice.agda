{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.Abstractions.Profunctors.Choice where

open import TypeTheory.Universes using (Type; 𝑢; usuc; Universe)
open import TypeTheory.SimpleTypes using (_compose_; id)
open import HoTT.Identity-Types using (refl; _≡_)
open import TypeTheory.Sum using (_+_; +comm; bimap+)
open import FP.Abstractions.Profunctor using (Profunctor; ProfunctorFunction)
open import FP.Types using (Function)

-- Choice profunctor (Cocartesian)
record Choice (_=>:_ : Type 𝑢 -> Type 𝑢 -> Type 𝑢) : Type (usuc 𝑢) where
  field
    isProfunctor : Profunctor _=>:_
    cleft : forall {A B C : Type 𝑢}
        -> (A =>: B)
        -> (A + C) =>: (B + C)
    -- TODO laws
  -- derived operations
  open Profunctor isProfunctor
  cright : forall {A B C : Type 𝑢}
        -> (A =>: B)
        -> (C + A) =>: (C + B)
  cright = (dimap +comm +comm) compose cleft

function-left : {A B C : Type 𝑢} -> Function A B -> Function (A + C) (B + C)
function-left f ac = bimap+ f id ac

ChoiceFunction : Choice {𝑢} Function
ChoiceFunction = record
  { isProfunctor = ProfunctorFunction
  ; cleft = function-left
  }
