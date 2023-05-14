{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module OrderTheory.PartialOrder where

open import TypeTheory.Universes using (Type; 𝑢)
open import HoTT.Identity-Types using (_≡_)
open import TypeTheory.Negation using (not)
open import Arithmetic.Nat-Relations using (
  _<_; trans-<; irreflexive<; asymmetric<;
  _>_; trans->; irreflexive>; asymmetric>
  )

-- partial order (poset)
record PartialOrder {X : Type 𝑢}(_rel_ : X -> X -> Type 𝑢) : Type 𝑢 where
  field
    irreflexive  : (x : X) -> not (x rel x)
    transitive : (x y z : X) -> x rel y -> y rel z -> x rel z
    asymmetric : (x y : X) -> x rel y -> not (y rel x)


Nat<PartialOrder : PartialOrder _<_
Nat<PartialOrder = record
  { irreflexive = irreflexive<
  ; transitive = trans-<
  ; asymmetric = asymmetric<
  }

Nat>PartialOrder : PartialOrder _>_
Nat>PartialOrder = record
  { irreflexive = irreflexive>
  ; transitive = trans->
  ; asymmetric = asymmetric>
  }
