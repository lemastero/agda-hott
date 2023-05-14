{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module OrderTheory.EquivalenceRel where

open import TypeTheory.Universes using (Type; 𝑢)
open import HoTT.Identity-Types using (
  _≡_; refl; ≡-refl; ≡-transitive; ≡-comm)


record EquivalenceRel {X : Type 𝑢}(_rel_ : X -> X -> Type 𝑢) : Type 𝑢 where
  field
    reflexive  : (x : X) -> x rel x
    transitive : {x y z : X} -> x rel y -> y rel z -> x rel z
    symmetric : {x y : X} -> (x rel y) -> (y rel x)

-- instances

≡EquivalenceRel : (X : Type 𝑢) -> EquivalenceRel (_≡_ {_} {X})
≡EquivalenceRel X = record
  { reflexive  = ≡-refl
  ; transitive = ≡-transitive
  ; symmetric  = ≡-comm
  }
