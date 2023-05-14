{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module OrderTheory.Preorder where

open import TypeTheory.Universes using (Type)
open import HoTT.Identity-Types using (_≡_; refl)

record Equivalence {X : Type}(_rel_ : X -> X -> Type) : Type where
  field
    reflexive  : {x : X} -> x rel x
    transitive : {x y z : X} -> x rel y -> y rel z -> x rel z
    symmetric : {x y : X} -> (x rel y) -> (y rel x)

record Preorder {X : Type}(_rel_ : X -> X -> Type) : Type where
  field
    reflexive  : {x : X} -> x rel x
    transitive : {x y z : X} -> x rel y -> y rel z -> x rel z
