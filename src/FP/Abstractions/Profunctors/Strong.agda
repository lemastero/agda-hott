{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.Abstractions.Profunctors.Strong where

open import TypeTheory.Universes using (Type; 𝑢; usuc; Universe)
open import TypeTheory.SimpleTypes using (id; _compose_; _andThen_)
open import HoTT.Identity-Types using (refl; _≡_)
open import TypeTheory.Product using (_×_; ×-comm; ×bimap)
open import FP.Abstractions.Profunctor
open import FP.Types using (Function)

-- Strong profunctor (Cartesian)
record Strong (_=>:_ : Type 𝑢 -> Type 𝑢 -> Type 𝑢) : Type (usuc 𝑢) where
  field
    isProfunctor : Profunctor _=>:_
    cFirst : forall {A B C : Type 𝑢}
        -> (A =>: B)
        -> (A × C) =>: (B × C)
    -- TODO laws
  -- derived operations
  open Profunctor isProfunctor
  cSecond : forall {A B C : Type 𝑢}
        -> (A =>: B)
        -> (C × A) =>: (C × B)
  cSecond = (dimap ×-comm ×-comm) compose cFirst

function-first : {A B C : Type 𝑢} -> Function A B -> Function (A × C) (B × C)
function-first f ac = ×bimap f id ac

StrongFunction : Strong {𝑢} Function
StrongFunction = record
  { isProfunctor = ProfunctorFunction
  ; cFirst = function-first
  }
