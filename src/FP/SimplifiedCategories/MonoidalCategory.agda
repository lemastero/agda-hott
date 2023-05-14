{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.SimplifiedCategories.MonoidalCategory where

open import TypeTheory.Universes using (Type; usuc; _umax_; Universe)
open import HoTT.Identity-Types using (_≡_)
open import FP.SimplifiedCategories.Bifunctor using (Bifunctor)
open import FP.SimplifiedCategories.Category using (Category)
open import TypeTheory.Product using (_×_)

-- agda-categories: https://github.com/agda/agda-categories/blob/master/src/Categories/Category/Monoidal/Core.agda
-- nlab: https://ncatlab.org/nlab/show/monoidal+category
private
  variable 𝑢C 𝑤C : Universe

record MonoidalCategory
     {Obj : Type 𝑢C}{_=>_ : Obj -> Obj -> Type 𝑤C}
     (M : Category Obj _=>_)
     (_⊗_ : Obj -> Obj -> Obj)
     (tensor : Bifunctor M M M _⊗_)
      : Type (usuc (𝑢C umax 𝑤C)) where

  open Bifunctor tensor
  open Category M
  -- TODO use natural isomorphism
  -- _<=>_ = {A B : Obj} -> ( A => B ) × ( B => A )

  -- tensor can map objects and morphisms
  -- ⊗    maps objects
  -- ⊗map maps morphisms
  _⊗map_ = bimap

  field

    I : Obj
    associator : forall {A B C : Obj}
               -> ((A ⊗ B) ⊗ C) => (A ⊗ (B ⊗ C))
    leftUnitor  : forall {A : Obj} -> (I ⊗ A) => A
    rightUnitor : forall {A : Obj} -> (A ⊗ I) => A

  {-
  -- helpers - unpack natural isomorphism
  associator  : forall {A B C : Type 𝑢} -> (A ⊗ B) ⊗ C -> A ⊗ (B ⊗ C)
  associator = (fst associatorEq)
  leftUnitor  : forall {A : Type 𝑢} -> (I ⊗ A) -> A
  leftUnitor = (fst leftUnitorEq)
  rightUnitor : forall {A : Type 𝑢} -> (A ⊗ I) -> A
  rightUnitor = (fst rightUnitorEq)
  -}

  -- helpers - bimap unitors and id
  rightUnitorLeft : forall {A B : Obj}
                 -> ((A ⊗ I) ⊗ B) => (A ⊗ B)
  rightUnitorLeft {A} {B} = (rightUnitor {A}) ⊗map (c-id B)

  leftUnitorRight : forall {A B : Obj} -> (A ⊗ (I ⊗ B)) => (A ⊗ B)
  leftUnitorRight {A} {B} = (c-id A) ⊗map (leftUnitor {B})

  -- helpers -- bimap associator and id

  associatorId : forall {A B C D : Obj} -> (((A ⊗ B) ⊗ C) ⊗ D) => ((A ⊗ (B ⊗ C)) ⊗ D)
  associatorId {A} {B} {C} {D} = (associator {A} {B} {C}) ⊗map (c-id D)

  idAssociator : forall {A B C D : Obj} -> (A ⊗ ((B ⊗ C) ⊗ D)) => (A ⊗ (B ⊗ (C ⊗ D)))
  idAssociator {A} {B} {C} {D} = (c-id A) ⊗map (associator {B} {C} {D})

  -- laws
  field
    triangleIdentity : forall {A B : Obj}
          -> (rightUnitorLeft {A} {B})             -- (A⊗I)⊗B  ->  A⊗B
               ≡
             ((associator {A} {I} {B}) c-andThen   -- (A⊗I)⊗B  ->  A⊗(I⊗B)
              (leftUnitorRight {A} {B})            -- A⊗(I⊗B)  ->  A⊗B
              )
    pentagonIdentity : forall {A B C D : Obj}
      -> ((associatorId {A} {B} {C} {D} c-andThen  -- ((A⊗B)⊗C)⊗D -> (A⊗(B⊗C))⊗D
          (associator {A} {B ⊗ C} {D})) c-andThen  -- (A⊗(B⊗C))⊗D -> A⊗((B⊗C)⊗D)
          idAssociator)                            -- A⊗((B⊗C)⊗D) -> A⊗(B⊗(C⊗D))
            ≡
          ((associator {A ⊗ B} {C} {D}) c-andThen  -- ((A⊗B)⊗C)⊗D -> (A⊗B)⊗(C⊗D)
           (associator {A} {B} {C ⊗ D}))           -- (A⊗B)⊗(C⊗D) -> A⊗(B⊗(C⊗D))
