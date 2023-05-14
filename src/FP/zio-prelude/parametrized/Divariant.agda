{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.zio-prelude.parametrized.Divariant where

open import TypeTheory.Universes using (Type; 𝑢; usuc; Universe)
open import TypeTheory.SimpleTypes using (id; _compose_)
open import TypeTheory.FunctionsProperties using (function-dimap-id; function-dimap-compose; compose3)
open import HoTT.Identity-Types using (refl; _≡_)
open import FP.Types using (Function)
open import FP.zio-prelude.parametrized.RightCovariant using (RightCovariant)

record LeftContravariant (F : Type 𝑢 -> Type 𝑢 -> Type 𝑢) : Type (usuc 𝑢) where
  field
    -- operations
    leftContramap : forall {A B AA : Type 𝑢}
        -> (AA -> A)
        -> F A B -> F AA B
    -- laws
    leftContramapIdentityLaw : forall {A : Type 𝑢}
          -> (fa : F A A)
          -> leftContramap id fa ≡ fa
    leftContramapComposeLaw : forall {A1 A2 A3 B1 : Type 𝑢}
          -> (f1 : (A2 -> A1))
          -> (f2 : (A3 -> A2))
          -> (fa : F A1 B1)
          -> leftContramap (f1 compose f2) fa ≡ leftContramap f2 (leftContramap f1 fa)


record Divariant (F : Type 𝑢 -> Type 𝑢 -> Type 𝑢) : Type (usuc 𝑢) where
  field
    -- operations
    dimap : forall {A B AA BB : Type 𝑢}
        -> (AA -> A)
        -> (B -> BB)
        -> F A B -> F AA BB
    -- laws
    dimapIdentityLaw : forall {A : Type 𝑢}
          -> (fa : F A A)
          -> dimap id id fa ≡ fa
    dimapComposeLaw : forall {A1 A2 A3 B1 B2 B3 : Type 𝑢}
          -> (f1 : (A2 -> A1))
          -> (f2 : (A3 -> A2))
          -> (g1 : (B1 -> B2))
          -> (g2 : (B2 -> B3))
          -> (fa : F A1 B1)
          -> dimap (f1 compose f2) (g2 compose g1) fa ≡ dimap f2 g2 (dimap f1 g1 fa)

  -- conversions

Divariant->RightCovariant : forall {F : Type 𝑢 -> Type 𝑢 -> Type 𝑢}
                         -> Divariant F
                         -> RightCovariant F
Divariant->RightCovariant D = record
  { rightMap            = (dimap D) id
  ; rightMapIdentityLaw = (dimapIdentityLaw D)
  ; rightMapComposeLaw  = (dimapComposeLaw D) id id
  } where open Divariant

Divariant->LeftContravariant : forall {F : Type 𝑢 -> Type 𝑢 -> Type 𝑢}
                            -> Divariant F
                            -> LeftContravariant F
Divariant->LeftContravariant D = record
  { leftContramap            = \ f -> (dimap D) f id
  ; leftContramapIdentityLaw = (dimapIdentityLaw D)
  ; leftContramapComposeLaw  = \ f1 f2 -> (dimapComposeLaw D) f1 f2 id id
  } where open Divariant

-- instances

DivariantFunction : Divariant {𝑢} Function
DivariantFunction = record
  { dimap            = \ f g h -> compose3 f h g
  ; dimapIdentityLaw = function-dimap-id
  ; dimapComposeLaw  = function-dimap-compose
  }
