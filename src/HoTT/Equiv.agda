{-# OPTIONS --without-K --exact-split --safe #-}

module HoTT.Equiv where

open import TypeTheory.Universes
open import TypeTheory.SimpleTypes
open import TypeTheory.Dependent-Types using (_Π-compose1_; Σ; Sigma)
open import HoTT.Identity-Types
open import HoTT.Homotopy
open import HoTT.Isomorphism

-- sec(f) := Σ g:B->A f . g ~ id
-- f is a split surjection
-- type of sections of f
record is-Section {A : Type 𝑢} {B : Type 𝑧} (f : A -> B) : Type (𝑢 umax 𝑧) where
  constructor
    Section
  field
    g        : B -> A
    sec-law  : (f Π-compose1 g) ~ id

-- retraction
-- f is a retraction of f
-- type of retractions of f
record is-Retraction {A : Type 𝑢} {B : Type 𝑧} (f : A -> B) : Type (𝑢 umax 𝑧) where
  constructor
    Retraction
  field
    h        : B -> A
    sec-law  : (h Π-compose1 f) ~ id

record is-equiv {A : Type 𝑢} {B : Type 𝑧} (f : A -> B) : Type (𝑢 umax 𝑧) where
  constructor
    Inverse
  field
    inverse  : B -> A
    η        : (inverse Π-compose1 f) ~ id
    inverse2 : B -> A
    ε        : (f Π-compose1 inverse2) ~ id

record _≃_ (A : Type 𝑢) (B : Type 𝑧) : Type (𝑢 umax 𝑧) where
  constructor
    Equivalence
  field
    map            : A -> B
    is-equivalence : is-equiv map

fwd : ∀ {A : Type 𝑢} {B : Type 𝑧} -> A ≃ B -> A -> B
fwd e = _≃_.map e

bwd : ∀ {A : Type 𝑢} {B : Type 𝑧} -> A ≃ B -> B -> A
bwd e = is-equiv.inverse (_≃_.is-equivalence e)

-- we can improve isomorphisms (bi-invertible maps) to equivalence
-- duplicate inverse g
iso-to-equiv : ∀ {A : Type 𝑢} {B : Type 𝑧} -> A ≅ B -> A ≃ B
iso-to-equiv (Isomorphism f (Inverse g gf fg)) =
  Equivalence f (Inverse g gf g fg)
