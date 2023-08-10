{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.Vec.Instances where

open import TypeTheory.Universes using (Type; 𝑢)
open import TypeTheory.SimpleTypes using (Nat)
open import FP.Vec using (Vec; vMap; vMap-id; vMap-compose; vec)
open import FP.Abstractions.Functor using (Functor)
open import FP.Abstractions.Applicative using (Applicative)

module _ (n : Nat) where
  instance
    FunctorVec : Functor {𝑢} (\ X -> Vec X n )
    FunctorVec = record
      { fmap         = vMap
      ; fmap-id      = vMap-id n
      ; fmap-compose = vMap-compose n
      }

instance
  FunctorVec1 : Functor {𝑢} (\ X -> Vec X 1 )
  FunctorVec1 = FunctorVec 1

  ApplicativeVec1 : Applicative {𝑢} (\ X -> Vec X 1 )
  ApplicativeVec1 = record
    { pure         = vec
    ; _<*>_        = {!   !}
    ; identity     = {!   !}
    ; composition  = {!   !}
    ; homomorphism = {!   !}
    ; interchange  = {!   !}
    }
