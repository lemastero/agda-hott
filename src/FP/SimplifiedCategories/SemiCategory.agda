{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.SimplifiedCategories.SemiCategory where

open import TypeTheory.Universes using (Type; 𝑢; usuc)
open import TypeTheory.SimpleTypes using (id; _compose_)
open import HoTT.Identity-Types using (refl; _≡_)
open import FP.Types using (Function)
open import TypeTheory.FunctionsProperties using (compose-assoc)

record SemiCategory (_=>_ : Type 𝑢 -> Type 𝑢 -> Type 𝑢) : Type (usuc 𝑢) where
  field
    -- operations
    _c-compose_ : forall {A B C : Type 𝑢}
        -> (B => C)
        -> (A => B)
        -> (A => C)
    -- laws
    compose-associativity-law : forall {A B C D : Type 𝑢}
          -> (f : (A => B))
          -> (g : (B => C))
          -> (h : (C => D))
          -> h c-compose (g c-compose f) ≡ (h c-compose g) c-compose f

SemiCategoryFunction : SemiCategory {𝑢} Function
SemiCategoryFunction = record
  { _c-compose_               = _compose_
  ; compose-associativity-law = \ f g h -> compose-assoc g f h
  }
