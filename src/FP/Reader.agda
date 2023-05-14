{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.Reader where

open import TypeTheory.Universes using (Type; 𝑢)
open import TypeTheory.SimpleTypes using (id; _compose_)
open import HoTT.Identity-Types using (_≡_; refl)

record Reader (R : Type 𝑢)(V : Type 𝑢) : Type 𝑢 where
  field
    run : (x : R) -> V
