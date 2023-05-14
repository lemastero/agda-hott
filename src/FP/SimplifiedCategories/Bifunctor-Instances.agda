{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

{-
agda-categories: https://github.com/agda/agda-categories/blob/master/src/Categories/Functor/Bifunctor.agda
cubical:
-}

module FP.SimplifiedCategories.Bifunctor-Instances where

open import FP.SimplifiedCategories.Category using (Category)
open import TypeTheory.Universes using (Universe; Type; _umax_)
open import TypeTheory.SimpleTypes using (id)
open import HoTT.Identity-Types using (refl; _≡_)
open import FP.SimplifiedCategories.Bifunctor using (Bifunctor; EndoBifunctor)
open import FP.SimplifiedCategories.Category-Instances using (FunctionCategory)
open import TypeTheory.Sum using (_+_; +right-id; +left-id; +id-right; +id-left
  ; +assocLR; +assocRL)

BifunctorProduct : Bifunctor FunctionCategory FunctionCategory FunctionCategory _×_
BifunctorProduct = ?

{-

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
-}
