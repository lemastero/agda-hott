{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module AbstractAlgebra.Magma where

open import TypeTheory.Universes using (Type; usuc; 𝑢)

record Magma : Type (usuc 𝑢) where
  field
    carrier        : Type 𝑢
    _⊕_            : carrier -> carrier -> carrier
  infixl 6 _⊕_
