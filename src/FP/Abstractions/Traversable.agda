{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

--https://github.com/pigworker/CS410-16/blob/master/lectures/CS410-Functor.agda

module FP.Abstractions.Traversable where

open import TypeTheory.Universes using (Type; 𝑢; usuc)
open import TypeTheory.SimpleTypes using (OneL; <>; unit; id; _compose_)
open import HoTT.Identity-Types using (refl; _≡_)
open import FP.Abstractions.Applicative using (Applicative)
open import FP.Types using (Id)

record Traversable (T : Type 𝑢 -> Type 𝑢) : Type (usuc 𝑢) where
  field
    -- operations
    traverse : forall {F}
            -> Applicative F
            -> forall {A B}
            -> (A -> F B)
            -> T A -> F (T B)
    -- TODO laws
  -- derived operations
  sequence : forall {F}
          -> Applicative F
          -> forall {A}
          -> T (F A)
          -> F (T A)
  sequence ApF fga = traverse ApF id fga
  fmap : forall {A B : Type 𝑢}
      -> (A -> B)
      -> T A -> T B
  fmap f fa = traverse ApplicativeId f fa
