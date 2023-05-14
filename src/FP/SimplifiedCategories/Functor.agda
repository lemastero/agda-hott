{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

{-
agda-categories: https://github.com/agda/agda-categories/blob/master/src/Categories/Functor/Core.agda
cubical:
-}

module FP.SimplifiedCategories.Functor where

open import FP.SimplifiedCategories.Category using (Category)
open import TypeTheory.Universes using (Universe; Type; _umax_)
open import TypeTheory.SimpleTypes using (id)
open import HoTT.Identity-Types using (refl; _≡_)

open Category

private
  variable 𝑢C 𝑤C 𝑢D 𝑤D : Universe

record Functor {ObjC : Type 𝑢C}{_=>C_ : ObjC -> ObjC -> Type 𝑤C}
               {ObjD : Type 𝑢D}{_=>D_ : ObjD -> ObjD -> Type 𝑤D}
               (C : Category ObjC _=>C_)
               (D : Category ObjD _=>D_)
               (F[_] : ObjC -> ObjD) : Type (𝑢C umax 𝑤C umax 𝑢D umax 𝑤D) where
  _composeC_ = _c-compose_ C
  _composeD_ = _c-compose_ D
  idC = c-id C
  idD = c-id D
  field
    -- operation
    fmap : {X Y : ObjC}       -- map on morphisms
         -> X =>C Y           -- morphism in C between X and Y
         -> F[ X ] =>D F[ Y ] -- morphism in D between FX and FY

    -- laws
    -- preserve identity
    F-identity : {X : ObjC} -> fmap (idC X) ≡ idD F[ X ]
    -- preserve composition (homomorphism)
    F-compose : {X S T : ObjC}
                (f : X =>C S)(g : S =>C T)
             -> fmap (g composeC f) ≡ (fmap g) composeD (fmap f)

{-
EndoFunctor : {ObjC : Type 𝑢C}{_=>C_ : ObjC -> ObjC -> Type 𝑤C}
           -> (Category ObjC _=>C_)
           -> Type (𝑢C umax 𝑤C)
EndoFunctor C = Functor C C
-}
IdFunctor : {ObjC : Type 𝑢C}{_=>C_ : ObjC -> ObjC -> Type 𝑤C}
           -> (C : Category ObjC _=>C_)
           -> Functor C C id
IdFunctor C = record
  { fmap       = id
  ; F-identity = refl _
  ; F-compose  = \ f g -> refl _
  } where open Category C
