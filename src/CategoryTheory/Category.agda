{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module CategoryTheory.Category where

open import TypeTheory.Universes using (usuc; _umax_; Type; Universe)
open import HoTT.Identity-Types using (_≡_)

{-
agda-categories: https://github.com/agda/agda-categories/blob/master/src/Categories/Category/Core.agda
cubical:         https://github.com/agda/cubical/blob/master/Cubical/Categories/Category/Base.agda
-}
record Category (𝑢 𝑤 : Universe) : Type (usuc (𝑢 umax 𝑤)) where
  field
    -- types
    Obj  : Type 𝑢                                     -- objects
    _~>_ : (source : Obj) -> (target : Obj) -> Type 𝑤 -- home object

    -- operations
    ~>id : {A : Obj} -> A ~> A                                -- identity
    _∘_  : {A B C : Obj} -> (A ~> B) -> (B ~> C) -> (A ~> C)  -- composition

    -- laws
    ∘left-id  : {A B : Obj} (f : A ~> B)
             -> (~>id ∘ f) ≡ f
    ∘right-id : {A B : Obj} (f : A ~> B)
             -> (f ∘ ~>id) ≡ f
    ∘assoc    : {A B C D : Obj} (f : A ~> B) (g : B ~> C) (h : C ~> D)
             -> (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)
    ∘assocLR  : {A B C D : Obj} (f : A ~> B) (g : B ~> C) (h : C ~> D)
             -> f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h
  infixr 3 _∘_
