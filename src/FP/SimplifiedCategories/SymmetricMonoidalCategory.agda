{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.SimplifiedCategories.SymmetricMonoidalCategory where

open import TypeTheory.Universes using (Type; 𝑢; usuc; Universe)
open import TypeTheory.SimpleTypes using (OneL; ZeroL; id; id'; _compose_; _andThen_)
open import HoTT.Identity-Types using (refl; _≡_)
open import FP.Types using (Function)
open import TypeTheory.FunctionsProperties using (compose-id; id-compose; compose-compose; compose-assoc)
open import FP.Abstractions.Bifunctor using (Bifunctor; BifunctorProduct; BifunctorEither; BifunctorThese)
open import FP.SimplifiedCategories.Category using (Category; CategoryFunction)
open import TypeTheory.Product using (_×_; ×assocLR; ×assocRL
  ; ×left-id; ×id-left; ×right-id; ×id-right; ×bimap)
open import TypeTheory.Sum using (_+_; +right-id; +left-id; +id-right; +id-left
  ; +assocLR; +assocRL)
open import FP.These using (These)
open import TypeTheory.LogicalEquiv using (_<=>_; <=>-fst)
open import TypeTheory.Product using (_,,_)
open import FP.SimplifiedCategories.MonoidalCategory using (MonoidalCategory)

-- https://ncatlab.org/nlab/show/symmetric+monoidal+category

record SymmetricMonoidalCategory (_⊗_ : Type 𝑢 -> Type 𝑢 -> Type 𝑢) : Type (usuc 𝑢) where
  field
    mc : MonoidalCategory {𝑢} _⊗_
    braiding : forall {A B : Type 𝑢} -> (A ⊗ B) <=> (B ⊗ A)
  open MonoidalCategory mc

  -- helpers - unpack equivalence
  swap : forall {A B : Type 𝑢} -> (A ⊗ B) -> (B ⊗ A)
  swap = (<=>-fst braiding)

  assocSwap : forall {A B C : Type 𝑢} -> (A ⊗ B) ⊗ C -> (B ⊗ C) ⊗ A
  assocSwap {A} {B} {C} = associator {A} {B} {C}
                        andThen
                        swap {A} {B ⊗ C}

  swapFirst : forall {A B C : Type 𝑢} -> (A ⊗ B) ⊗ C -> (B ⊗ A) ⊗ C
  swapFirst {A} {B} {C} = (swap {A} {B}) ⊗map id' C

  swapFirstAssoc : forall {A B C : Type 𝑢} -> (A ⊗ B) ⊗ C -> B ⊗ (A ⊗ C)
  swapFirstAssoc {A} {B} {C} = swapFirst {A} {B} {C} andThen associator {B} {A} {C}

  swapSecond : forall {A B C : Type 𝑢} -> A ⊗ (B ⊗ C) -> A ⊗ (C ⊗ B)
  swapSecond {A} {B} {C} = id' A ⊗map swap {B} {C}

  -- laws
  field
    swapIdentity : forall {A B : Type 𝑢}
               -> (swap {A} {B}) compose (swap {B} {A}) ≡ id
    hexagonIdentity : forall {A B C : Type 𝑢}
          -> assocSwap {A} {B} {C}
             andThen
             (associator {B} {C} {A})
               ≡
             (swapFirstAssoc {A} {B} {C} andThen swapSecond {B} {A} {C})
