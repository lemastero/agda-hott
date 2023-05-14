{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module CategoryTheory.Category.Construction.OppositeCategory where

open import TypeTheory.Universes using (Type; Universe; 𝑢; 𝑤)
open import TypeTheory.Dependent-Types using (flip; flip3)
open import HoTT.Identity-Types using (_≡_; ≡-sym; refl)
open import CategoryTheory.Category using (Category)

{-
nLab:            https://ncatlab.org/nlab/show/opposite+category
agda-categories: https://github.com/agda/agda-categories/blob/master/src/Categories/Category/Core.agda#L94
cubical:         https://github.com/agda/cubical/blob/master/Cubical/Categories/Category/Base.agda#L130
-}

open Category

OppositeCategory : Category 𝑢 𝑤 -> Category 𝑢 𝑤
OppositeCategory cat = record
  { Obj       = Obj cat
  ; _~>_      = flip (_~>_ cat)
  ; ~>id      = ~>id cat
  ; _∘_       = flip (_∘_ cat)
  ; ∘left-id  = ∘right-id cat
  ; ∘right-id = ∘left-id cat
  ; ∘assoc    = flip3 (∘assocLR cat)
  ; ∘assocLR  = flip3 (∘assoc cat)
  }

-- opposite category is involution
op-involutive : forall (C : Category 𝑢 𝑤) ->
               OppositeCategory (OppositeCategory C) ≡ C
op-involutive = refl
