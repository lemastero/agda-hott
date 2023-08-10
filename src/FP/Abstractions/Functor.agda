{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.Abstractions.Functor where

open import TypeTheory.Universes using (Type; 𝑢; usuc; Universe)
open import TypeTheory.SimpleTypes using (OneL; <>; unit; id; _compose_; Nat)
open import TypeTheory.FunctionsProperties using (compose-id; compose-compose)
open import HoTT.Identity-Types using (refl; _≡_)
open import FP.Types using (Id; Function)

record Functor (F : Type 𝑢 -> Type 𝑢) : Type (usuc 𝑢) where
  field
    -- operations
    fmap : forall {A B : Type 𝑢}
        -> (A -> B)
        -> F A -> F B
    -- laws
    fmap-id : forall {A : Type 𝑢}
          -> (fa : F A)
          -> fmap id fa ≡ fa
    fmap-compose : forall {A B C : Type 𝑢}
          -> (f : (A -> B))
          -> (g : (B -> C))
          -> (fa : F A)
          -> fmap (g compose f) fa ≡ fmap g (fmap f fa)
  -- derived operations
  void : forall {A : Type 𝑢}
      -> F A
      -> F OneL
  void = fmap unit

instance
  FunctorId : Functor {𝑢} Id
  FunctorId = record
    { fmap = id
    ; fmap-id = refl
    ; fmap-compose = \ f g fa -> refl (g (f fa))
    }

  FunctorFunction : {X : Type 𝑢} -> Functor {𝑢} (Function X)
  FunctorFunction {X} = record
    { fmap         = _compose_
    ; fmap-id      = compose-id
    ; fmap-compose = compose-compose
    }
