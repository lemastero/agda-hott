{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.SimplifiedCategories.MonoidObject where

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
open import AbstractAlgebra.Monoid using (Monoid)
open import FP.SimplifiedCategories.MonoidalCategory using (MonoidalCategory)

-- https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category

record MonoidObject (_⊗_ : Type 𝑢 -> Type 𝑢 -> Type 𝑢) : Type (usuc 𝑢) where
  field
    mc : MonoidalCategory {𝑢} _⊗_
  open MonoidalCategory mc

  field
    M : Type 𝑢          -- carrier object
    moUnit    : I -> M
    moCompose : M ⊗ M -> M

  -- utitities
  moUnit-id : (I ⊗ M) -> (M ⊗ M)
  moUnit-id = moUnit ⊗map id

  id-moUnitId : (M ⊗ I) -> (M ⊗ M)
  id-moUnitId = id ⊗map moUnit

  id-moCompose :  M ⊗ (M ⊗ M) -> (M ⊗ M)
  id-moCompose = id ⊗map moCompose

  moCompose-id : (M ⊗ M) ⊗ M -> (M ⊗ M)
  moCompose-id = moCompose ⊗map id

  -- laws
  field
    mo-associativity-law :
      (moCompose-id andThen              -- (M ⊗ M) ⊗ M  ->  (M ⊗ M)
        moCompose)                       -- M ⊗ M        ->  M
      ≡
      ((associator {M} {M} {M}) andThen  -- (M ⊗ M) ⊗ M  ->  M ⊗ (M ⊗ M)
         id-moCompose) andThen           -- M ⊗ (M ⊗ M)  ->  (M ⊗ M)
         moCompose                       -- M ⊗ M        ->  M
    mo-left-identity-law :
      (moUnit-id andThen   -- I -> M
        moCompose)         -- M ⊗ M   ->  M
      ≡ leftUnitor {M}     -- I ⊗ M   -> A

    mo-right-identity-law :
      (id-moUnitId andThen   -- (M ⊗ I) -> (M ⊗ M)
        moCompose)           -- M ⊗ M   ->  M
      ≡ rightUnitor {M}      -- (M ⊗ I) -> M
