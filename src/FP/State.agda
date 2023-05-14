{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.State where

open import TypeTheory.Universes using (Type; 𝑢)
open import TypeTheory.SimpleTypes using (id; _compose_)
open import HoTT.Identity-Types using (_≡_; refl)
open import TypeTheory.Product using (_×_)

record State (S : Type 𝑢)(A : Type 𝑢) : Type 𝑢 where
  field
    runState : (x : S) -> A × S
