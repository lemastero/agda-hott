{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module CategoryTheory.Functor.Presheaf where

open import TypeTheory.Universes using (_umax_; Type; Universe)
open import CategoryTheory.Category using (Category)
open import CategoryTheory.Category.Construction.OppositeCategory using (OppositeCategory)
open import CategoryTheory.Functor using (Functor)

private
  variable 𝑢C 𝑤C 𝑢D 𝑤D : Universe

{-
nLab:            https://ncatlab.org/nlab/show/presheaf
agda-categories: https://github.com/agda/agda-categories/blob/master/src/Categories/Functor/Presheaf.agda
cubical:         https://github.com/agda/cubical/blob/master/Cubical/Categories/Presheaf/Base.agda
-}

Presheaf : (C : Category 𝑢C 𝑤C) (D : Category 𝑢D 𝑤D) -> Type (𝑢C umax 𝑤C umax 𝑢D umax 𝑤D)
Presheaf C D = Functor (OppositeCategory C) D
