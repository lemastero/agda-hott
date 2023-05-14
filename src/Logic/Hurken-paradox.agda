{-# OPTIONS --without-K --type-in-type #-}
{-
Hurkens' paradox
encoded in Agda by HoTT-UF-0-2-Hurken-para
original: https://github.com/martinescardo/HoTTEST-Summer-School/blob/main/Agda/Auxiliary/Hurkens.lagda.md
-}

module Logic.Hurken-paradox where

open import TypeTheory.Universes

P : Type -> Type
P X = X -> Type

PP : Type -> Type
PP X = P (P X)

False : Type
False = (X : Type) -> X

not : Type -> Type
not X = X -> False

U : Type
U = (X : Type) -> (PP X -> X) -> PP X

tau : PP U -> U
tau t X f p = t \ x -> p (f (x X f))

rho : U -> PP U
rho s = s U \ t -> tau t

delta : P U
delta y = not ((p : P U) -> rho y p -> p (tau (rho y)))

omega : U
omega = tau \ p -> (x : U) -> rho x p -> p x

D : Type
D = (p : P U) -> rho omega p -> p (tau (rho omega))

lemma : (p : P U) -> ((x : U) -> rho x p -> p x) -> p omega
lemma p H = H omega \ x -> H (tau (rho x))

nd : not D
nd = lemma delta \ x H K -> K delta H \ p -> K \ y -> p (tau (rho y))

d : D
d p = lemma \ y -> p (tau (rho y))

boom : False
boom = nd d

--- example 1

data Void : Type where

inhabit-empty-type : Void
inhabit-empty-type = boom Void

-- example 2

data Nat : Type where
  zero : Nat
  succ : Nat -> Nat

one = succ zero

data _≡_ {X : Type} : X -> X -> Type where
  refl : (x : X) -> x ≡ x

one-is-zero : one ≡ zero
one-is-zero = boom (one ≡ zero)
