{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.Id.Instances where

open import TypeTheory.Universes using (Type; 𝑢)
open import TypeTheory.SimpleTypes using (id)
open import HoTT.Identity-Types using (refl)
open import FP.Abstractions.Functor using (Functor)
open import FP.Types using (Id)

instance
  FunctorId : Functor {𝑢} Id
  FunctorId = record
    { fmap = id
    ; fmap-id = refl
    ; fmap-compose = \ f g fa -> refl (g (f fa))
    }
