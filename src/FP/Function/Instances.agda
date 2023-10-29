{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.Function.Instances where

open import TypeTheory.Universes using (Type; 𝑢)
open import TypeTheory.SimpleTypes using (OneL; <>; unit; id; _compose_; Nat)
open import TypeTheory.FunctionsProperties using (compose-id; compose-compose)
open import TypeTheory.FunctionsProperties using (function-dimap-id; function-dimap-compose; compose3)
open import FP.Types using (Function)
open import FP.Abstractions.Functor using (Functor)
open import FP.Abstractions.Profunctor using (Profunctor)

instance
  FunctorFunction : {X : Type 𝑢} -> Functor {𝑢} (Function X)
  FunctorFunction {X} = record
    { fmap         = _compose_
    ; fmap-id      = compose-id
    ; fmap-compose = compose-compose
    }

  ProfunctorFunction : Profunctor {𝑢} Function
  ProfunctorFunction = record
    { dimap         = \ f g h -> compose3 f h g
    ; dimap-id      = function-dimap-id
    ; dimap-compose = function-dimap-compose
    }
