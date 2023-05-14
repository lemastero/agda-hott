{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.Abstractions.Optics.Prism where

open import TypeTheory.Universes using (Type; 𝑢)
open import TypeTheory.SimpleTypes using (id; _compose_)
open import HoTT.Identity-Types using (_≡_; refl)
open import TypeTheory.Product using (_×_)

record Prism (A : Type 𝑢)(B : Type 𝑢)(S : Type 𝑢)(T : Type 𝑢) : Type 𝑢 where
  field
    match : S -> T × A
    build : B -> T
