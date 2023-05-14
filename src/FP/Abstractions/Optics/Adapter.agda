{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.Abstractions.Optics.Adapter where

open import TypeTheory.Universes using (Type; 𝑢)
open import TypeTheory.SimpleTypes using (id; _compose_)
open import HoTT.Identity-Types using (_≡_; refl)
open import TypeTheory.Product using (_×_)

record Adapter (A : Type 𝑢)(B : Type 𝑢)(S : Type 𝑢)(T : Type 𝑢) : Type 𝑢 where
  field
    from : S -> A
    to   : B -> T
