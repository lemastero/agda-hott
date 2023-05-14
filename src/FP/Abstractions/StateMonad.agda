{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.Abstractions.StateMonad where

open import TypeTheory.Universes using (Type; 𝑢; usuc; Universe)
open import TypeTheory.SimpleTypes using (const; id)

record StateMonad (F : Type 𝑢 -> Type 𝑢)(S : Type 𝑢) : Type (usuc 𝑢) where
  field
    -- operations
    update : (S -> S) -> F S
    -- laws
  -- derived operations
  set : S -> F S
  set s = update (const s)
  fetch : F S
  fetch = update id
