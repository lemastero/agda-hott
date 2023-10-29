{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.Either.Instances where

open import TypeTheory.Universes using (Type; 𝑢)
open import TypeTheory.Sum using (_+_)
open import TypeTheory.SimpleTypes using (Nat; succ; zero; id; _compose_)
open import FP.List using (List; map-List; map-id; map-compose; list; _<*>_)
open import FP.Abstractions.Functor using (Functor)
open import FP.Abstractions.Applicative using (Applicative)
open import FP.Abstractions.Monad using (Monad)

module _ (E : Type 𝑢) where
  instance
    FunctorEither : Functor {𝑢} (\ A -> E + A)
    FunctorEither = record
      { fmap         = {!   !}
      ; fmap-id      = {!   !}
      ; fmap-compose = {!   !}
      }

    ApplicativeEither : Applicative {𝑢} (\ A -> E + A)
    ApplicativeEither = record
      { pure         = {!   !}
      ; _<*>_        = {!   !}
      ; identity     = {!   !}
      ; composition  = {!   !}
      ; homomorphism = {!   !}
      ; interchange  = {!   !}
      }

    MonadEither : Monad {𝑢} (\ A -> E + A)
    MonadEither = record
      { return = {!   !}
      ; _>>=_ = {!   !}
      ; return-flatmap = {!   !}
      ; flatmap-return = {!   !}
      ; flatmap-compose = {!   !}
      }
