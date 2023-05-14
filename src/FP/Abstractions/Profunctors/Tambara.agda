{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.Abstractions.Profunctors.Tambara where

open import TypeTheory.Universes using (Type; 𝑢; usuc; Universe)

record Tambara (_=>:_ : Type 𝑢 -> Type 𝑢 -> Type 𝑢)
               (_*x_ : Type 𝑢 -> Type 𝑢 -> Type 𝑢) : Type (usuc 𝑢) where
  field
    runTambara : forall {A B C : Type 𝑢}
        -> (A =>: B)
        -> (A *x C) =>: (B *x C)
