{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.zio-prelude.parametrized.Bicovariant where

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
open import FP.zio-prelude.parametrized.RightCovariant using (RightCovariant)

record LeftCovariant (F : Type 𝑢 -> Type 𝑢 -> Type 𝑢) : Type (usuc 𝑢) where
  field
    -- operations
    leftMap : forall {A B AA : Type 𝑢}
        -> (A -> AA)
        -> F A B -> F AA B
    -- laws
    leftMapIdentityLaw : forall {A : Type 𝑢}
          -> (fa : F A A)
          -> leftMap id fa ≡ fa
    leftMapComposeLaw : forall {A1 A2 A3 B1 : Type 𝑢}
          -> (f1 : (A1 -> A2))
          -> (f2 : (A2 -> A3))
          -> (fa : F A1 B1)
          -> leftMap (f2 compose f1) fa ≡ leftMap f2 (leftMap f1 fa)

-- Bifunctor
record Bicovariant (F : Type 𝑢 -> Type 𝑢 -> Type 𝑢) : Type (usuc 𝑢) where
  field
    -- operations
    bimap : forall {A B AA BB : Type 𝑢}
        -> (A -> AA)
        -> (B -> BB)
        -> F A B -> F AA BB
    -- laws
    bimapIdentityLaw : forall {A : Type 𝑢}
          -> (fa : F A A)
          -> bimap id id fa ≡ fa
    bimapComposeLaw : forall {A1 A2 A3 B1 B2 B3 : Type 𝑢}
          -> (f1 : (A1 -> A2))
          -> (f2 : (A2 -> A3))
          -> (g1 : (B1 -> B2))
          -> (g2 : (B2 -> B3))
          -> (fa : F A1 B1)
          -> bimap (f2 compose f1) (g2 compose g1) fa ≡ bimap f2 g2 (bimap f1 g1 fa)

-- conversions

Bicovariant->RightCovariant : forall {F : Type 𝑢 -> Type 𝑢 -> Type 𝑢}
                           -> Bicovariant F
                           -> RightCovariant F
Bicovariant->RightCovariant BF = record
   { rightMap            = (bimap BF) id
   ; rightMapIdentityLaw = (bimapIdentityLaw BF)
   ; rightMapComposeLaw  = (bimapComposeLaw BF) id id
   } where open Bicovariant

Bicovariant->LeftCovariant : forall {F : Type 𝑢 -> Type 𝑢 -> Type 𝑢}
                          -> Bicovariant F -> LeftCovariant F
Bicovariant->LeftCovariant BF = record
  { leftMap            = \ g -> (bimap BF) g id
  ; leftMapIdentityLaw = (bimapIdentityLaw BF)
  ; leftMapComposeLaw  = \ f1 f2 -> (bimapComposeLaw BF) f1 f2 id id
  } where open Bicovariant

-- instances

BicovariantProduct : Bicovariant {𝑢} _×_
BicovariantProduct = record
  { bimap         = ×bimap
  ; bimapIdentityLaw      = ×bimap-id
  ; bimapComposeLaw = ×bimap-compose
  }

BicovariantSum : Bicovariant {𝑢} _+_
BicovariantSum = record
  { bimap         = bimap+
  ; bimapIdentityLaw      = bimap+id
  ; bimapComposeLaw = bimap+compose
  }

BicovariantThese : Bicovariant {𝑢} These
BicovariantThese = record
  { bimap         = bimap-These
  ; bimapIdentityLaw      = bimap-These-id
  ; bimapComposeLaw = bimap-These-compose
  }

BicovariantValidated : Bicovariant {𝑢} Validated
BicovariantValidated = record
  { bimap         = bimap-Validated
  ; bimapIdentityLaw      = Validated-bimap-id
  ; bimapComposeLaw = Validated-map-compose
  }
