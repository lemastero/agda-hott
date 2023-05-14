{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.zio-prelude.parametrized.Contravariant where

open import TypeTheory.Universes using (Type; 𝑢; usuc; Universe)
open import TypeTheory.SimpleTypes using (OneL; <>; unit; id; _compose_; _andThen_)
open import TypeTheory.FunctionsProperties using (compose-id; compose-assoc)
open import HoTT.Identity-Types using (refl; _≡_)
open import FP.Maybe using (Maybe; map-Maybe; maybe-map-id; maybe-map-compose)
open import FP.Types using (Function)

-- zio-prelude
-- https://github.com/zio/zio-prelude/blob/series/2.x/core/shared/src/main/scala/zio/prelude/Contravariant.scala
-- https://github.com/zio/zio-prelude/blob/series/2.x/laws/shared/src/main/scala/zio/prelude/laws/ContravariantLaws.scala

record Contravariant (F : Type 𝑢 -> Type 𝑢) : Type (usuc 𝑢) where
  field
    -- operations
    contramap : forall {A B : Type 𝑢}
        -> (B -> A)
        -> F A -> F B
    -- laws
    identityLaw : forall {A : Type 𝑢}
          -> (fa : F A)
          -> contramap id fa ≡ fa
    compositionLaw : forall {A B C : Type 𝑢}
          -> (f : (B -> A))
          -> (g : (C -> B))
          -> (fa : F A)
          -> contramap (f compose g) fa ≡ contramap g (contramap f fa)
  -- TODO Contravariant Functor composition

ContravariantFunction : (X : Type 𝑢) -> Contravariant {𝑢} \ A -> Function A X
ContravariantFunction X = record
  { contramap      = _andThen_
  ; identityLaw    = compose-id
  ; compositionLaw = compose-assoc
  }
