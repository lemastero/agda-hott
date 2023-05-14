{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.Abstractions.Yoneda where

open import TypeTheory.Universes using (Type; 𝑢; usuc; Universe)
open import HoTT.Identity-Types using (refl; _≡_)
open import TypeTheory.SimpleTypes using (id)
open import FP.Abstractions.Functor using (Functor)

record Yoneda (F : Type 𝑢 -> Type 𝑢)(A : Type 𝑢) : Type (usuc 𝑢) where
  field
    -- operations
    runYoneda : forall {R : Type 𝑢}
        -> (A -> R)
        -> F R
    -- laws
  -- derived operations
  lowerYoneda : F A
  lowerYoneda = runYoneda id

open Functor

liftYoneda : {F : Type 𝑢 -> Type 𝑢}{A : Type 𝑢}
          -> F A
          -> Functor F
          -> Yoneda F A
liftYoneda fa FF = record {
  runYoneda = \ f  -> (fmap FF) f fa
  }
