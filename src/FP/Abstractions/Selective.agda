{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

--https://github.com/pigworker/CS410-16/blob/master/lectures/CS410-Functor.agda

module FP.Abstractions.Selective where

open import TypeTheory.Universes using (Type; 𝑢; usuc)
open import TypeTheory.SimpleTypes using (OneL; <>; unit; id; _compose_)
open import HoTT.Identity-Types using (refl; _≡_)
open import FP.Types using (Id)

record Selective (F : Type 𝑢 -> Type 𝑢) : Type (usuc 𝑢) where
  field
    -- operations
    select : forall {A B : Type 𝑢} -> F (A + B) -> F (A -> B) -> F B
    -- TODO laws https://github.com/tuura/selective-theory-agda/blob/master/src/Selective.agda#L137

 
