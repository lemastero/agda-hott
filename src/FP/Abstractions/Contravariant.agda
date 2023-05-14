{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.Abstractions.Contravariant where

open import TypeTheory.Universes using (Type; 𝑢; usuc; Universe)
open import TypeTheory.SimpleTypes using (OneL; <>; unit; id; _compose_; _andThen_)
open import TypeTheory.FunctionsProperties using (compose-id; compose-assoc)
open import HoTT.Identity-Types using (refl; _≡_)
open import FP.Maybe using (Maybe; map-Maybe; maybe-map-id; maybe-map-compose)
open import FP.Types using (Function)

{- https://github.com/pigworker/CS410-16/blob/master/lectures/CS410-Functor.agda -}

record Contravariant (F : Type 𝑢 -> Type 𝑢) : Type (usuc 𝑢) where
  field
    -- operations
    contramap : forall {A B : Type 𝑢}
        -> (B -> A)
        -> F A -> F B
    -- laws
    contramap-id : forall {A : Type 𝑢}
          -> (fa : F A)
          -> contramap id fa ≡ fa
    contramap-compose : forall {A B C : Type 𝑢}
          -> (f : (B -> A))
          -> (g : (C -> B))
          -> (fa : F A)
          -> contramap (f compose g) fa ≡ contramap g (contramap f fa)

ContravariantFunction : (X : Type 𝑢) -> Contravariant {𝑢} \ A -> Function A X
ContravariantFunction X = record
  { contramap         = _andThen_
  ; contramap-id      = compose-id
  ; contramap-compose = compose-assoc
  }
