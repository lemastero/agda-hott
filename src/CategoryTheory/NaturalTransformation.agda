{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module CategoryTheory.NaturalTransformation where

open import TypeTheory.Universes using (_umax_; Type; Universe)
open import CategoryTheory.Category using (Category)
open import CategoryTheory.Functor using (Functor)
open import HoTT.Identity-Types using (_≡_)

open Functor
open Category

private
  variable
    𝑢C 𝑤C 𝑢D 𝑤D : Universe

{-
agda-categories: https://github.com/agda/agda-categories/blob/master/src/Categories/NaturalTransformation/Core.agda
cubical: https://github.com/agda/cubical/blob/master/Cubical/Categories/NaturalTransformation/Base.agda

https://github.com/pigworker/CS410-18/blob/master/Lib/Cat/NatTrans.agda
https://github.com/pigworker/CS410-17/blob/master/exercises/CS410-Categories.agda#L133
-}
record NaturalTransformation {C : Category 𝑢C 𝑤C}
                             {D : Category 𝑢D 𝑤D}
                             (F G : Functor C D) : Type (𝑢C umax 𝑤C umax 𝑢D umax 𝑤D) where
  field
    -- operation (component of natural transformation)
    transform : (X : Obj C) -> _~>_ D (F-Obj F X) (F-Obj G X)

    -- law
    naturality : forall {X Y : Obj C}
              -> (f : _~>_ C X Y)
              -> (_∘_ D) (F-map F f) (transform Y) ≡ (_∘_ D) (transform X) (F-map G f)
