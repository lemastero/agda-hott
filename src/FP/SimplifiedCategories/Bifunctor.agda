{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

{-
agda-categories: https://github.com/agda/agda-categories/blob/master/src/Categories/Functor/Bifunctor.agda
cubical:
-}

module FP.SimplifiedCategories.Bifunctor where

open import FP.SimplifiedCategories.Category using (Category)
open import TypeTheory.Universes using (Universe; Type; _umax_; 𝑢)
open import TypeTheory.SimpleTypes using (id)
open import HoTT.Identity-Types using (refl; _≡_)

open Category

private
  variable 𝑢C 𝑤C 𝑢D 𝑤D 𝑢E 𝑤E : Universe

-- TODO define Bifunctor as Functor (CatProduct C D) E
-- TODO define Bifunctor as Functor C E x Functor C E
-- TODO prove they are =
record Bifunctor
               {ObjC : Type 𝑢C}{_=>C_ : ObjC -> ObjC -> Type 𝑤C}
               {ObjD : Type 𝑢D}{_=>D_ : ObjD -> ObjD -> Type 𝑤D}
               {ObjE : Type 𝑢E}{_=>E_ : ObjE -> ObjE -> Type 𝑤E}
               (C : Category ObjC _=>C_)
               (D : Category ObjD _=>D_)
               (E : Category ObjE _=>E_)
               (B[_,_] : ObjC -> ObjD -> ObjE)
                 : Type (𝑢C umax 𝑤C umax 𝑢D umax 𝑤D umax 𝑢E umax 𝑤E) where
  _andThenC_ = _c-andThen_ C
  _andThenD_ = _c-andThen_ D
  _andThenE_ = _c-andThen_ E
  idC = c-id C
  idD = c-id D
  idE = c-id E
  field
    -- operation
    bimap : {X XX : ObjC} {Y YY : ObjD}       -- map on morphisms:
         -> X =>C XX           -- morphism in C between X and Y
         -> Y =>D YY
         -> B[ X , Y ] =>E B[ XX , YY ] -- morphism in D between FX and FY

    -- laws
    -- preserve identity
    B-identity : {X : ObjC}{Y : ObjD} -> bimap (idC X) (idD Y) ≡ idE B[ X , Y ]
    -- preserve composition (homomorphism)
    B-compose : {X1 X2 X3 : ObjC} {Y1 Y2 Y3 : ObjD}
                (f1 : X1 =>C X2)(f2 : X2 =>C X3)
                (g1 : Y1 =>D Y2)(g2 : Y2 =>D Y3)
             -> bimap (f1 andThenC f2) (g1 andThenD g2) ≡ (bimap f1 g1) andThenE (bimap f2 g2)

EndoBifunctor : {Obj : Type 𝑢C}{_=>_ : Obj -> Obj -> Type 𝑤C}
          -> (Category Obj _=>_)
          -> (B[_,_] : Obj -> Obj -> Obj)  -- Agda is confused when missing
          -> Type (𝑢C umax 𝑤C)
EndoBifunctor C B = Bifunctor C C C B

-- identity that takes 2 arguments have choice can pick right argument
id3r : {A : Type 𝑢} -> (A -> A -> A)
id3r _ = id

-- ... or left
id3l : {A : Type 𝑢} -> (A -> A -> A)
id3l a _ = a

-- we can define identity bifunctor in 2 different ways
IdBifunctor : {Obj : Type 𝑢C}{_=>_ : Obj -> Obj -> Type 𝑤C}
           -> (C : (Category Obj _=>_))
           -> Bifunctor C C C id3r
IdBifunctor C = record
  { bimap      = \ f g -> g
  ; B-identity = refl _
  ; B-compose  = \ f1 f2 g1 g2 -> refl _
  }

IdBifunctorL : {Obj : Type 𝑢C}{_=>_ : Obj -> Obj -> Type 𝑤C}
           -> (C : (Category Obj _=>_))
           -> Bifunctor C C C id3l
IdBifunctorL C = record
  { bimap      = \ f g -> f
  ; B-identity = refl _
  ; B-compose  = \ f1 f2 g1 g2 -> refl _
  }
