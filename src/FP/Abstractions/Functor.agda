{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.Abstractions.Functor where

open import TypeTheory.Universes using (Type; 𝑢; usuc; Universe)
open import TypeTheory.SimpleTypes using (OneL; <>; unit; id; _compose_; Nat)
open import TypeTheory.FunctionsProperties using (compose-id; compose-compose)
open import HoTT.Identity-Types using (refl; _≡_)
open import FP.Maybe using (Maybe; map-Maybe; maybe-map-id; maybe-map-compose)
open import FP.List using (List; []; _cons_; map-List; map-id; map-compose)
open import FP.Vec using (Vec; vMap; vMap-id; vMap-compose)
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

FunctorId : Functor {𝑢} Id
FunctorId = record
  { fmap = id
  ; fmap-id = refl
  ; fmap-compose = \ f g fa -> refl (g (f fa))
  }

FunctorMaybe : Functor {𝑢} Maybe
FunctorMaybe = record
  { fmap         = map-Maybe
  ; fmap-id      = maybe-map-id
  ; fmap-compose = maybe-map-compose
  }

FunctorList : Functor {𝑢} List
FunctorList = record
  { fmap         = map-List
  ; fmap-id      = map-id
  ; fmap-compose = map-compose
  }

FunctorVec : (n : Nat) -> Functor {𝑢} (\ X -> Vec X n )
FunctorVec n = record
  { fmap         = vMap
  ; fmap-id      = vMap-id n
  ; fmap-compose = vMap-compose n
  }

FunctorFunction : {X : Type 𝑢} -> Functor {𝑢} (Function X)
FunctorFunction {X} = record
  { fmap         = _compose_
  ; fmap-id      = compose-id
  ; fmap-compose = compose-compose
  }
