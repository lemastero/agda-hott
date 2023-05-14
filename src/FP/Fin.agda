{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.Fin where

open import TypeTheory.Universes using (Type)
open import TypeTheory.SimpleTypes using (Nat; succ)

data Fin : Nat -> Type where
  fzero : (n : Nat) -> Fin (succ n)
  fsucc : (n : Nat) -> Fin n -> Fin (succ n)
