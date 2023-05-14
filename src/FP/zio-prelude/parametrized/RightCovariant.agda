{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.zio-prelude.parametrized.RightCovariant where

open import TypeTheory.Universes using (Type; 𝑢; usuc; Universe)
open import TypeTheory.SimpleTypes using (OneL; <>; unit; id; _compose_)
open import HoTT.Identity-Types using (refl; _≡_)
open import FP.These using (These; bimap-These; This; That; Those;
  bimap-These-id; bimap-These-compose)
open import FP.Validated using
  (Validated; bimap-Validated; Success; Error;
   Validated-bimap-id; Validated-map-compose)
open import TypeTheory.Sum using (_+_; left; right; bimap+; bimap+id; bimap+compose)
open import TypeTheory.Product using (_×_; ×bimap; ×bimap-compose; ×bimap-id)
open import FP.Types using (Function)

record RightCovariant (F : Type 𝑢 -> Type 𝑢 -> Type 𝑢) : Type (usuc 𝑢) where
  field
    -- operations
    rightMap : forall {A B BB : Type 𝑢}
        -> (B -> BB)
        -> F A B -> F A BB
    -- laws
    rightMapIdentityLaw : forall {A : Type 𝑢}
          -> (fa : F A A)
          -> rightMap id fa ≡ fa
    rightMapComposeLaw : forall {A1 B1 B2 B3 : Type 𝑢}
          -> (g1 : (B1 -> B2))
          -> (g2 : (B2 -> B3))
          -> (fa : F A1 B1)
          -> rightMap (g2 compose g1) fa ≡ rightMap g2 (rightMap g1 fa)
