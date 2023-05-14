{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module AbstractAlgebra.Monoid where

open import TypeTheory.Universes
open import TypeTheory.SimpleTypes
open import HoTT.Identity-Types using (_≡_)
open import Arithmetic.Nat-Peano
open import FP.List using (List; _concat_; []; _cons_;
  concat-nil; nil-concat; concat-assoc)

record Monoid : Type (usuc 𝑢) where
  field
    carrier        : Type 𝑢
    Unit           : carrier
    _⊕_            : carrier -> carrier -> carrier

    ⊕right-unit : forall (x : carrier) -> x ⊕ Unit ≡ x
    ⊕left-unit  : forall (x : carrier) -> Unit ⊕ x ≡ x
    ⊕assoc      : forall (x y z : carrier) -> (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
  infixl 6 _⊕_

Monoid-Nat+0 : Monoid
Monoid-Nat+0 = record
  { carrier = Nat
  ; Unit        = 0
  ; _⊕_         = _+_
  ; ⊕right-unit = +right-identity
  ; ⊕left-unit  = +left-identity
  ; ⊕assoc      = assocLR-+
  }

Monoid-Nat*1 : Monoid
Monoid-Nat*1 = record
  { carrier     = Nat
  ; Unit        = 1
  ; _⊕_         = _*_
  ; ⊕right-unit = *right-identity
  ; ⊕left-unit  = *left-identity
  ; ⊕assoc      = assocLR-*
  }

Monoid-List-concat : (X : Type) -> Monoid
Monoid-List-concat X = record
  { carrier     = List X
  ; Unit        = []
  ; _⊕_         = _concat_
  ; ⊕right-unit = concat-nil
  ; ⊕left-unit  = nil-concat
  ; ⊕assoc      = concat-assoc
  }
