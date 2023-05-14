{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module AbstractAlgebra.Semigroup where

open import TypeTheory.Universes
open import TypeTheory.SimpleTypes
open import HoTT.Identity-Types using (_≡_)
open import Arithmetic.Nat-Peano
open import FP.List using (List; _concat_; []; _cons_;
  concat-nil; nil-concat; concat-assoc)

record Semigroup : Type (usuc 𝑢) where
  constructor Semi
  field
    carrier        : Type 𝑢
    _⊕_            : carrier -> carrier -> carrier
    ⊕assoc         : (x y z : carrier)
                  -> (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
  infixl 6 _⊕_

Semigroup-Nat+0 : Semigroup
Semigroup-Nat+0 = record
  { carrier = Nat
  ; _⊕_         = _+_
  ; ⊕assoc      = assocLR-+
  }

Semigroup-Nat*1 : Semigroup
Semigroup-Nat*1 = record
  { carrier     = Nat
  ; _⊕_         = _*_
  ; ⊕assoc      = assocLR-*
  }

Semigroup-List-concat : (X : Type) -> Semigroup
Semigroup-List-concat X = record
  { carrier     = List X
  ; _⊕_         = _concat_
  ; ⊕assoc      = concat-assoc
  }
