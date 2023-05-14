{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module OrderTheory.Semilattice where

open import TypeTheory.Universes using (Type)
open import HoTT.Identity-Types using (_≡_; refl)

record Semilattice {X : Type}(_leq_ : X -> X -> Type)(_relSum_ : X -> X -> X) : Type where
  field
    reflexive  : {x : X} -> x leq x
    transitive : {x y z : X} -> x leq y -> y leq z -> x leq z
    law1 : {x y : X} -> x leq (x relSum y)
    law2 : {x y : X} -> y leq (x relSum y)
    law3 : {x y z : X} -> x leq y -> y leq z -> (z relSum y) leq z
