{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module CategoryTheory.Category.Construction.DiscreteCategory where

open import TypeTheory.Universes using (usuc; _umax_; Type; Universe; 𝑢1; 𝑢0; 𝑢)
open import HoTT.Identity-Types using (_≡_; refl)
open import CategoryTheory.Category using (Category)
open import HoTT.Homotopy-Levels using (is-set)

private
  variable 𝑢C 𝑤C 𝑢D 𝑤D : Universe

-- discrete category
-- objects - elements of given type X that is homotopy set (elements equality is proposition)
-- morphisms - only identity morphism from equality
DiscreteCategory : (X : Type 𝑢)
                -> is-set X
                -> Category 𝑢 𝑢
DiscreteCategory X isSet = record
  { Obj       = X
  ; _~>_      = _≡_
  ; ~>id      = \ {X} -> refl X
  ; _∘_       = \ {R} {S} {T} -> \ { (refl R) (refl R) -> refl R }
  ; ∘left-id  = \ {s} {t} f -> (isSet s t) _ f
  ; ∘right-id = \ {s} {t} f -> (isSet s t) _ f
  ; ∘assoc    = \ {q} {r} {s} {t} f g h -> (isSet q t) _ _
  ; ∘assocLR  = \ {q} {r} {s} {t} f g h -> (isSet q t) _ _
  }
