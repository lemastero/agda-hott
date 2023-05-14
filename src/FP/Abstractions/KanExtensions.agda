{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.Abstractions.KanExtensions where

open import TypeTheory.Universes using (Type; 𝑢; usuc; Universe)
open import HoTT.Identity-Types using (refl; _≡_)
open import TypeTheory.SimpleTypes using (id)
open import FP.Abstractions.Functor using (Functor)

record Codensity (F : Type 𝑢 -> Type 𝑢)(A : Type 𝑢) : Type (usuc 𝑢) where
  field
    -- operations
    runRan : forall {B : Type 𝑢}
        -> (A -> F B)
        -> F B

record Ran (G : Type 𝑢 -> Type 𝑢)
           (H : Type 𝑢 -> Type 𝑢)
           (A : Type 𝑢) : Type (usuc 𝑢) where
  field
    -- operations
    runRan : forall {B : Type 𝑢}
        -> (A -> G B)
        -> H B

Ran->Codensity : (F : Type 𝑢 -> Type 𝑢)(A : Type 𝑢)
              -> Ran F F A -> Codensity F A
Ran->Codensity F A ran = record { runRan = \ f -> Ran.runRan ran f }
