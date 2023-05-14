{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.Kleisli where

open import TypeTheory.Universes using (Type; 𝑢)
open import TypeTheory.SimpleTypes using (id; _compose_)
open import HoTT.Identity-Types using (_≡_; refl)

record Kleisli (F : Type 𝑢 -> Type 𝑢)(A : Type 𝑢)(B : Type 𝑢) : Type 𝑢 where
  field
    runKleisli : (x : A) -> F B
