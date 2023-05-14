{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module CategoryTheory.Category.Category-Instances where

open import TypeTheory.Universes using (usuc; _umax_; Type; Universe; 𝑢1; 𝑢0; 𝑢)
open import TypeTheory.SimpleTypes using
  (One; <>; Nat; succ; zero; id; _andThen_; _compose_; ->-assoc)
open import FP.Fin using (Fin)
open import HoTT.Identity-Types
  using (_≡_; refl; ≡-refl; ->left-identity; ->right-identity; ->assocRL; ->assocLR)
open import Arithmetic.Nat-Peano using
  ( _+_; _*_;
   +left-identity; +right-identity; assocLR-+;
   *left-identity; *right-identity; assocLR-*)
open import Arithmetic.Nat-Relations using (_>=_; refl->=; trans->= )
open import CategoryTheory.Category using (Category)
open import HoTT.Homotopy-Levels using (is-proposition)

private
  variable 𝑢C 𝑤C 𝑢D 𝑤D : Universe

-- Set
-- objects types
-- morphisms pure functions
CategorySetFunction : Category 𝑢1 𝑢0
CategorySetFunction = record
  { Obj       = Type
  ; _~>_      = \ x y -> x -> y
  ; ~>id      = id
  ; _∘_       = _andThen_
  ; ∘left-id  = ->left-identity
  ; ∘right-id = ->right-identity
  ; ∘assoc    = ->assocRL
  ; ∘assocLR  = ->assocLR
  }

>=-is-proposition : forall (n m : Nat) -> is-proposition (n >= m)
>=-is-proposition zero zero <> <> = refl <>
>=-is-proposition (succ n) zero <> <> = refl <>
>=-is-proposition (succ n) (succ m) p q = >=-is-proposition n m p q

-- TODO define for any Preorder (reflexive, transitive relation)
-- object - natural numbers
-- morphisms - max one, exists if n >= m (degenerated morphisms)
-- TODO is Thin category same as this? https://github.com/agda/agda-categories/blob/master/src/Categories/Category/Construction/Thin.agda
CategoryNat>= : Category 𝑢0 𝑢0
CategoryNat>= = record
  { Obj  = Nat
  ; _~>_ = _>=_
  ; ~>id = \ {n} -> refl->= n
  ; _∘_  = \ {m} {n} {p} m>=n n>=p -> trans->= m n p m>=n n>=p
  ; ∘left-id =  \ {s} {t} f -> >=-is-proposition s t _ _ --(trans->= {s} {s} {t} (refl->= {s}) f) f
  ; ∘right-id = \ {s} {t} f -> >=-is-proposition s t _ _ --(trans->= {s} {t} {t} f (refl->= {t})) f
  ; ∘assoc = \ {q} {r} {s} {t} f g h ->
      >=-is-proposition q t _ _
        -- (trans->= {q} {s} {t} (trans->= {q} {r} {s} f g) h)
        -- (trans->= {q} {r} {t} f (trans->= {r} {s} {t} g h))
  ; ∘assocLR  = \ {q} {r} {s} {t} f g h -> >=-is-proposition q t _ _
  }

{- https://github.com/agda/agda-categories/blob/master/src/Categories/Category/Instance/Nat.agda -}
CategoryNatFin : Category 𝑢0 𝑢0
CategoryNatFin = record
  { Obj       = Nat
  ; _~>_      = \ m n -> (Fin m -> Fin n)
  ; ~>id      = id
  ; _∘_       = _andThen_
  ; ∘left-id  = ->left-identity
  ; ∘right-id = ->right-identity
  ; ∘assoc    = ->assocRL
  ; ∘assocLR  = ->assocLR
  }
