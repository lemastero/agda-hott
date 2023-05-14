{-# OPTIONS --without-K --exact-split --safe #-}

module HoTT.Isomorphism where

open import TypeTheory.Universes
open import TypeTheory.SimpleTypes
open import TypeTheory.Dependent-Types using (_Π-compose1_; Σ; Sigma)
open import HoTT.Homotopy

record is-bijection {A : Type 𝑢} {B : Type 𝑧} (f : A -> B) : Type (𝑢 umax 𝑧) where
  constructor
    Inverse
  field
    inverse : B -> A
    η       : (inverse Π-compose1 f) ~ id
    ε       : (f Π-compose1 inverse) ~ id

record _≅_ (A : Type 𝑢) (B : Type 𝑧) : Type (𝑢 umax 𝑧) where
  constructor
    Isomorphism
  field
    bijection   : A -> B
    bijectivity : is-bijection bijection

infix 0 _≅_
