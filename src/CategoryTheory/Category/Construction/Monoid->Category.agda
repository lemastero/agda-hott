{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module CategoryTheory.Category.Construction.Monoid->Category where

open import TypeTheory.Universes using (Type; 𝑢0)
open import TypeTheory.SimpleTypes using (One)
open import HoTT.Identity-Types using (_≡_; ≡-sym)
open import CategoryTheory.Category using (Category)
open import AbstractAlgebra.Monoid using (Monoid; Monoid-Nat*1; Monoid-Nat+0)

open Monoid

{-
agda-categories: https://github.com/agda/agda-categories/blob/master/src/Categories/Category/Construction/MonoidAsCategory.agda
-}

-- Monoid as Category
-- one object (degenerated objects)
-- morphisms are values of monoid, composition is monoid operation
Monoid->Category : Type 𝑢0 -> Monoid -> Category 𝑢0 𝑢0
Monoid->Category ob m = record
  { Obj       = ob
  ; _~>_      = \ x y -> carrier m
  ; ~>id      = Unit m
  ; _∘_       = _⊕_ m
  ; ∘left-id  = ⊕left-unit m
  ; ∘right-id = ⊕right-unit m
  ; ∘assoc    = ⊕assoc m
  ; ∘assocLR  = \ f g h -> ≡-sym ((⊕assoc m) f g h)
  }

Monoid->CategoryOne : Monoid -> Category 𝑢0 𝑢0
Monoid->CategoryOne = Monoid->Category One

Monoid*->Category : Category 𝑢0 𝑢0
Monoid*->Category = Monoid->CategoryOne Monoid-Nat*1

Monoid+->Category : Category 𝑢0 𝑢0
Monoid+->Category = Monoid->CategoryOne Monoid-Nat+0
