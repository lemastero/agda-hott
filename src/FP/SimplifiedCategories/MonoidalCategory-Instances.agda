{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.SimplifiedCategories.MonoidalCategory-Instances where

open import TypeTheory.Universes using (Type; 𝑢; usuc; Universe)
open import TypeTheory.SimpleTypes using (OneL; ZeroL; id; id'; _compose_; _andThen_)
open import HoTT.Identity-Types using (refl; _≡_)
open import FP.SimplifiedCategories.Bifunctor using (Bifunctor; BifunctorProduct; BifunctorEither; BifunctorThese)
open import FP.SimplifiedCategories.Category using (Category; CategoryFunction)
open import TypeTheory.Product using (_×_; ×assocLR; ×assocRL
  ; ×left-id; ×id-left; ×right-id; ×id-right; ×bimap; _,,_)
open import TypeTheory.Sum using (_+_; +right-id; +left-id; +id-right; +id-left
  ; +assocLR; +assocRL)
open import FP.SimplifiedCategories.MonoidalCategory using (MonoidalCategory)
open import FP.SimplifiedCategories.MonoidObject  using (MonoidObject)
open import AbstractAlgebra.Monoid using (Monoid)

-- Monoidal Category instances
triangleIdentity-product : {A B : Type 𝑢}
  ->
  ×bimap ×right-id (id' B)
    ≡
  (×bimap (id' A) ×left-id compose ×assocLR)
triangleIdentity-product {𝑢} {A} {B} = {!   !}

MonoidalCategoryTuple : MonoidalCategory {𝑢} _×_
MonoidalCategoryTuple = record
  { isCategory       = CategoryFunction
  ; tensor           = BifunctorProduct
  ; I                = OneL
  ; associatorEq     = ( ×assocLR  ,, ×assocRL )
  ; leftUnitorEq     = ( ×left-id  ,, ×id-left )
  ; rightUnitorEq    = ( ×right-id ,, ×id-right )
  ; triangleIdentity = triangleIdentity-product
  ; pentagonIdentity = {!   !}
  }

MonoidalCategoryEither : MonoidalCategory {𝑢} _+_
MonoidalCategoryEither = record
  { isCategory       = CategoryFunction
  ; tensor           = BifunctorEither
  ; I                = ZeroL
  ; associatorEq     = ( +assocLR  ,, +assocRL )
  ; leftUnitorEq     = ( +left-id  ,, +id-left )
  ; rightUnitorEq    = ( +right-id ,, +id-right )
  ; triangleIdentity = {!   !}
  ; pentagonIdentity = {!   !}
  }

  -- Monoid object instances

MonoidObjectMonoid : Monoid -> MonoidObject {𝑢} _×_
MonoidObjectMonoid Mon = record
  { mc        = MonoidalCategoryTuple
  ; M         = {! Unit  !}
  ; moUnit    = {!   !}
  ; moCompose = {!   !}
  ; mo-associativity-law  = {!   !}
  ; mo-left-identity-law  = {!   !}
  ; mo-right-identity-law = {!   !}
  } where open Monoid Mon
