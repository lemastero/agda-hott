{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.List.Instances where

open import TypeTheory.Universes using (Type; 𝑢)
open import TypeTheory.SimpleTypes using (Nat; succ; zero; id; _compose_)
open import FP.List using (
  List;
  map-List;
  flatMap-List;
  map-id; map-compose; list; _<*>_)
open import FP.Abstractions.Functor using (Functor)
open import FP.Abstractions.Applicative using (Applicative)
open import FP.Abstractions.Monad using (Monad)

instance
  FunctorList : Functor {𝑢} List
  FunctorList = record
    { fmap         = map-List
    ; fmap-id      = map-id
    ; fmap-compose = map-compose
    }

  ApplicativeList : Applicative {𝑢} List
  ApplicativeList = record
    { pure         = list
    ; _<*>_        = _<*>_
    ; identity     = {!   !}
    ; composition  = {!   !}
    ; homomorphism = {!   !}
    ; interchange  = {!   !}
    }

  MonadList : Monad {𝑢} List
  MonadList = record
    { return = list
    ; _>>=_ = \ xs f -> flatMap-List f xs
    ; return-flatmap = {!   !}
    ; flatmap-return = {!   !}
    ; flatmap-compose = {!   !}
    }
