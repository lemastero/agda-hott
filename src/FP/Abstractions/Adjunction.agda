{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.Abstractions.Adjunction where

open import TypeTheory.Universes using (Type; 𝑢; usuc; Universe)
open import HoTT.Identity-Types using (refl; _≡_)
open import TypeTheory.SimpleTypes using (id)
open import FP.Abstractions.Functor using (Functor)

record Adjunction (F : Type 𝑢 -> Type 𝑢)
                  (G : Type 𝑢 -> Type 𝑢) : Type (usuc 𝑢) where
  field
    left : forall {A B : Type 𝑢}
        -> (F A -> B)
        -> A -> G B
    right : forall {A B : Type 𝑢}
        -> (A -> G B)
        -> F A -> B
