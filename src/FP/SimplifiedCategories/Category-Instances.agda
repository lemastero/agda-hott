{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.SimplifiedCategories.Category-Instances where

open import TypeTheory.Universes using (Type; 𝑢; 𝑤; usuc; _umax_; 𝑢1; 𝑢0)
open import TypeTheory.SimpleTypes using (id; _andThen_; Nat; zero; succ; <>)
open import TypeTheory.FunctionsProperties using (compose-id; id-compose; andThen-assoc)
open import HoTT.Identity-Types using (refl; _≡_)
open import HoTT.Homotopy-Levels using (is-proposition)
open import FP.Types using (Function)
open import FP.SimplifiedCategories.Category using (Category)
open import Arithmetic.Nat-Relations using (_>=_; refl->=; trans->=)

-- category of types and functions (think Hask, Scala)
FunctionCategory : Category Type Function
FunctionCategory = record
  { c-id             = id _
  ; _c-andThen_      = _andThen_
  ; C-left-identity  = compose-id
  ; C-right-identity = id-compose
  ; C-associativity  = andThen-assoc
  }

>=-is-proposition : forall (n m : Nat) -> is-proposition (n >= m)
>=-is-proposition zero zero <> <> = refl <>
>=-is-proposition (succ n) zero <> <> = refl <>
>=-is-proposition (succ n) (succ m) p q = >=-is-proposition n m p q

-- TODO Universes fails when I use def below in Category Nat >=

>=-andThen : {n m k : Nat}
          -> (n>=m : n >= m)
          -> (m>=k : m >= k)
          -> (n >= k)
>=-andThen {n} {m} {k} = trans->= n m k

>=-left-id : {n m : Nat}
          -> (p : n >= m)
          -> trans->= n n m (refl->= n) p ≡ p
>=-left-id {n} {m} p = >=-is-proposition n m _ _

Nat>=Category : Category Nat _>=_
Nat>=Category = record
  { c-id             = \ n -> refl->= n
  ; _c-andThen_      = \ {n} {m} {k} -> trans->= n m k
  ; C-left-identity  = \ {n} {m} p -> >=-is-proposition n m _ _
  ; C-right-identity = \ {n} {m} p -> >=-is-proposition n m _ _
  ; C-associativity  = \ {m} {n} {k} {l} p q r -> >=-is-proposition m l _ _ -- TODO
  }
