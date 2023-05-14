{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.Abstractions.Bifunctor where

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

record Bifunctor (F : Type 𝑢 -> Type 𝑢 -> Type 𝑢) : Type (usuc 𝑢) where
  field
    -- operations
    _bimap_ : forall {A B AA BB : Type 𝑢}
        -> (A -> AA)
        -> (B -> BB)
        -> F A B -> F AA BB
    -- laws
    bimap-id-law : forall {A : Type 𝑢}
          -> (fa : F A A)
          -> (id bimap id) fa ≡ fa
    bimap-compose-law : forall {A1 A2 A3 B1 B2 B3 : Type 𝑢}
          -> (f1 : (A1 -> A2))
          -> (f2 : (A2 -> A3))
          -> (g1 : (B1 -> B2))
          -> (g2 : (B2 -> B3))
          -> (fa : F A1 B1)
          -> ((f2 compose f1) bimap (g2 compose g1)) fa ≡ (f2 bimap g2) ((f1 bimap g1) fa)
  -- derived operations
  rmap : forall {A B BB : Type 𝑢}
      -> (B -> BB)
      -> F A B -> F A BB
  rmap = id bimap_
  lmap : forall {A B AA : Type 𝑢}
      -> (A -> AA)
      -> F A B -> F AA B
  lmap g = g bimap id
  -- derived laws
  rmap-id-law : forall {A : Type 𝑢}
        -> (fa : F A A)
        -> rmap id fa ≡ fa
  rmap-id-law = bimap-id-law
  rmap-compose-law : forall {A1 B1 B2 B3 : Type 𝑢}
        -> (g1 : (B1 -> B2))
        -> (g2 : (B2 -> B3))
        -> (fa : F A1 B1)
        -> rmap (g2 compose g1) fa ≡ rmap g2 (rmap g1 fa)
  rmap-compose-law = bimap-compose-law id id
  lmap-id-law : forall {A : Type 𝑢}
        -> (fa : F A A)
        -> lmap id fa ≡ fa
  lmap-id-law = bimap-id-law
  lmap-compose-law : forall {A1 A2 A3 B1 : Type 𝑢}
        -> (f1 : (A1 -> A2))
        -> (f2 : (A2 -> A3))
        -> (fa : F A1 B1)
        -> lmap (f2 compose f1) fa ≡ lmap f2 (lmap f1 fa)
  lmap-compose-law f1 f2 = bimap-compose-law f1 f2 id id


BifunctorProduct : Bifunctor {𝑢} _×_
BifunctorProduct = record
  { _bimap_           = ×bimap
  ; bimap-id-law      = ×bimap-id
  ; bimap-compose-law = ×bimap-compose
  }

BifunctorEither : Bifunctor {𝑢} _+_
BifunctorEither = record
  { _bimap_           = bimap+
  ; bimap-id-law      = bimap+id
  ; bimap-compose-law = bimap+compose
  }

BifunctorThese : Bifunctor {𝑢} These
BifunctorThese = record
  { _bimap_           = bimap-These
  ; bimap-id-law      = bimap-These-id
  ; bimap-compose-law = bimap-These-compose
  }

BifunctorValidated : Bifunctor {𝑢} Validated
BifunctorValidated = record
  { _bimap_           = bimap-Validated
  ; bimap-id-law      = Validated-bimap-id
  ; bimap-compose-law = Validated-map-compose
  }
