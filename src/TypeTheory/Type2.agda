{-# OPTIONS --without-K --exact-split --safe #-}

module TypeTheory.Type2 where

open import TypeTheory.Universes
open import TypeTheory.SimpleTypes
open import TypeTheory.Sum

-- two point type (Bool) defined using binary sum and One type
2T : Type 𝑢0
2T = One + One

pattern Zero' = left <>
pattern One' = right <>

2T-induction : (P : 2T -> Type 𝑢)
 -> P Zero'
 -> P One'
 -> (n : 2T) -> P n
2T-induction P p0 p1 Zero' = p0
2T-induction P p0 p1 One' = p1

2T-induction' : (P : 2T -> Type 𝑢)
 -> P Zero'
 -> P One'
 -> (n : 2T) -> P n
2T-induction' P p0 p1 = +elim
  P
  (1-elim (\ x -> P (left x))  p0 )
  (1-elim (\ y -> P (right y)) p1 )

2T-recursion : (P : Type 𝑢)
 -> P
 -> (2T -> P -> P)
 -> 2T -> P
2T-recursion P p f t2 = 2T-induction (\ 2t -> P) p (f t2 p) t2

-- TODO proove something about 2T-recurion is equiv to Bool-recursion ?
