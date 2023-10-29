{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.Maybe.Instances where

open import TypeTheory.Universes using (Type; 𝑢)
open import TypeTheory.SimpleTypes using (Nat; succ; zero; id; _compose_)
open import FP.List using (List; map-List; map-id; map-compose; list; _<*>_)
open import FP.Maybe using (
  Maybe;
  map-Maybe; maybe-map-id; maybe-map-compose;
  Just;
  flatMap-Maybe;
  maybe-flatMap-just-f; maybe-flatMap-f-just; maybe-flatMap-compose)
open import FP.Abstractions.Functor using (Functor)
open import FP.Abstractions.Applicative using (Applicative)
open import FP.Abstractions.Monad using (Monad)

instance
  FunctorMaybe : Functor {𝑢} Maybe
  FunctorMaybe = record
    { fmap         = map-Maybe
    ; fmap-id      = maybe-map-id
    ; fmap-compose = maybe-map-compose
    }

  ApplicativeMaybe : Applicative {𝑢} Maybe
  ApplicativeMaybe = record
    { pure         = {!   !}
    ; _<*>_        = {!   !}
    ; identity     = {!   !}
    ; composition  = {!   !}
    ; homomorphism = {!   !}
    ; interchange  = {!   !}
    }

  MonadMaybe : Monad {𝑢} Maybe
  MonadMaybe = record
    { return = Just
    ; _>>=_ = flatMap-Maybe
    ; return-flatmap = maybe-flatMap-just-f
    ; flatmap-return = maybe-flatMap-f-just
    ; flatmap-compose = maybe-flatMap-compose
    }
