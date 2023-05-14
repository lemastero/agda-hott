{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module AbstractAlgebra.Group where

open import TypeTheory.Universes
open import TypeTheory.SimpleTypes
open import HoTT.Identity-Types
open import Arithmetic.Nat-Peano
open import HoTT.Homotopy-Levels
open import Arithmetic.Int

record Group : Type (usuc 𝑢) where
  field
    carrier        : Type 𝑢
    Unit           : carrier
    _⊕_            : carrier -> carrier -> carrier
    -*_            : carrier -> carrier

    ⊕right-unit : (x : carrier)     -> x ⊕ Unit ≡ x
    ⊕left-unit  : (x : carrier)     -> Unit ⊕ x ≡ x
    ⊕assoc      : (x y z : carrier)
               -> x ⊕ (y ⊕ z) ≡ (x ⊕ y) ⊕ z
    -left-inv   : (x : carrier)
              -> x ⊕ (-* x) ≡ Unit
    -riht-inv   : (x : carrier)
              -> (-* x) ⊕ x ≡ Unit
  infixl 6 _⊕_
