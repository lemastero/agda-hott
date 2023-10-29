{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.Abstractions.Profunctor where

open import TypeTheory.Universes using (Type; 𝑢; usuc; Universe)
open import TypeTheory.SimpleTypes using (unit; id; _compose_; _andThen_)
open import HoTT.Identity-Types using (refl; _≡_)

record Profunctor (F : Type 𝑢 -> Type 𝑢 -> Type 𝑢) : Type (usuc 𝑢) where
  field
    -- operations
    dimap : forall {A B AA BB : Type 𝑢}
        -> (AA -> A)
        -> (B -> BB)
        -> F A B -> F AA BB
    -- laws
    dimap-id : forall {A : Type 𝑢}
          -> (fa : F A A)
          -> dimap id id fa ≡ fa
    dimap-compose : forall {A1 A2 A3 B1 B2 B3 : Type 𝑢}
          -> (f1 : (A2 -> A1))
          -> (f2 : (A3 -> A2))
          -> (g1 : (B1 -> B2))
          -> (g2 : (B2 -> B3))
          -> (fa : F A1 B1)
          -> dimap (f1 compose f2) (g2 compose g1) fa ≡ dimap f2 g2 (dimap f1 g1 fa)
  -- derived operations
  map : forall {A B BB : Type 𝑢}
        -> (B -> BB)
        -> F A B -> F A BB
  map = dimap id
  contramap : forall {A B AA : Type 𝑢}
      -> (AA -> A)
      -> F A B -> F AA B
  contramap f = dimap f id
  -- derived operations laws
  map-id : forall {A : Type 𝑢}
        -> (fa : F A A)
        -> map id fa ≡ fa
  map-id = dimap-id
  contramap-id : forall {A : Type 𝑢}
        -> (fa : F A A)
        -> contramap id fa ≡ fa
  contramap-id = dimap-id
