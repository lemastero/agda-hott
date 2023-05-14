{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module Arithmetic.Nat-Peano where

open import TypeTheory.Universes using (Type)
open import TypeTheory.SimpleTypes using (Zero; One; Nat; succ; zero)
open import TypeTheory.Sum renaming (_+_ to _\/_)
open import TypeTheory.Dependent-Types
open import HoTT.Identity-Types using (_≡_; refl; cong; ≡-comm; ap)
open import TypeTheory.Negation using (_≡/_; One-is-not-Zero)

-- operators

_+_ : Nat -> Nat -> Nat
a + zero     = a
a + (succ b) = succ (a + b)

_*_ : Nat -> Nat -> Nat
a * zero     = zero
a * (succ b) = a + (a * b)

_^_ : Nat -> Nat -> Nat
a ^ zero     = 1
a ^ (succ b) = a * (a ^ b)

-- predecesor (inverse of succ)
pred : Nat -> Nat
pred zero     = zero
pred (succ n) = n

-- properties

{- Peano arithmetic axioms: forall n,a,b
 0 != succ n                 positive-not-zero
 succ a = succ b => a ≡ b    succ-Id-to-Id
 n + 0 = n                   +right-identity
 a + succ b = succ (a + b)   succ-distribute-+R
 n * 0 = 0                   *-zero
 a * succ b = (a * b) + a    succ-distribute-*R

Robinson arithmetic axioms = Peano arithmetic with 1 extra axiom
  y=0 or exists x. succ x = y

Arithmetic axioms from abstract algebra:
  (x + y) + z = x + (y + Z)        addition is associative
  x + y = y + x                    addition is commutative
  (x * y) * z = x * (y * z)        multiplication is associative
  x * y = y * x                    multiplicatio is commutative
  x * (y + z) = (x * y) + (x * z)  mutiplication distributes over addition
  x + 0 = x                        zero is identity for addition
  x * 0 = 0                        zero is absorbing element for multiplication
  x * 1 = x                        1 is identity for multiplication
-}

isSucc : Nat -> Type0
isSucc zero     = Zero
isSucc (succ n) = One

positive-not-zero : (x : Nat) -> (succ x ≡/ 0)
positive-not-zero x succ_x=0 =
  One-is-not-Zero (succIsZeroAbsurd succ_x=0)
    where
      succIsZeroAbsurd : succ x ≡ 0 -> One ≡ Zero
      succIsZeroAbsurd n = ap isSucc n

-- succ is left cancellable
succ-Id-to-Id : (a b : Nat) -> (succ a) ≡ (succ b) -> (a ≡ b)
succ-Id-to-Id a a (refl (succ a)) = refl a
--succ-Id-to-Id a b = ap pred

-- properties + succ

succ-distribute-+R : (n m : Nat)
                    ---------------------------
                 -> (n + succ m) ≡ succ (n + m)
succ-distribute-+R n m = refl (succ (n + m))

succ-distribute-+L : (n m : Nat)
                    ---------------------------
                 -> (succ n + m) ≡ succ (n + m)
succ-distribute-+L n zero = refl (succ n)
succ-distribute-+L n (succ m)
  rewrite succ-distribute-+L n m = refl (succ (succ (n + m)))

-- properties of +

+left-identity : (n : Nat)
                 ---------------
              -> (zero + n) ≡ n
+left-identity zero     = refl zero
+left-identity (succ n) = cong succ (+left-identity n)

+right-identity : (n : Nat)
                  --------------
               -> (n + zero) ≡ n
+right-identity n = refl n

comm-+ : (x y : Nat)
         -----------------
      -> (x + y) ≡ (y + x)
comm-+ x zero
  rewrite +left-identity x = refl x
comm-+ x (succ y)
  rewrite comm-+ x y
  | succ-distribute-+L y x = refl (succ (y + x))

assocLR-+ : (x y z : Nat)
            -----------------------------
         -> ((x + y) + z) ≡ (x + (y + z))
assocLR-+ x y zero = refl (x + y)
assocLR-+ x y (succ z) = cong succ (assocLR-+ x y z)

assocRL-+ : (x y z : Nat)
            -----------------------------
         -> (x + (y + z)) ≡ ((x + y) + z)
assocRL-+ x y z = ≡-comm (assocLR-+ x y z)

-- properties * succ

succ-distribute-*R : (n m : Nat)
                    ----------------------------
                 -> (n * succ m) ≡ ((n * m) + n)
succ-distribute-*R n m
  rewrite comm-+ n (n * m) = refl ((n * m) + n)

succ-distribute-* : (n m : Nat)
                    ----------------------------
                 -> (succ n * m) ≡ (m + (n * m))
succ-distribute-* n zero = refl zero
succ-distribute-* n (succ m)
  rewrite succ-distribute-* n m
  | assocRL-+ (succ n) m (n * m)
  | assocRL-+ (succ m) n (n * m)
  | succ-distribute-+L n m
  | succ-distribute-+L m n
  | comm-+ m n = refl (succ (n + m) + (n * m))

-- properties of *

*right-identity : (n : Nat)
        -----------
     -> (n * 1) ≡ n
*right-identity n = refl n

*left-identity : (n : Nat)
        -----------
     -> (1 * n) ≡ n
*left-identity zero = refl 0
*left-identity (succ n)
  rewrite *left-identity n | comm-+ 1 n  = refl (succ n)

*-zero : (n : Nat)
         -----------------
      -> (n * zero) ≡ zero
*-zero zero = refl zero
*-zero (succ n-times-0) rewrite *-zero n-times-0 = refl zero

zero-* : (n : Nat)
         -----------------
      -> (zero * n) ≡ zero
zero-* zero = refl zero
zero-* (succ n) rewrite zero-* n = refl zero

comm-* : (x y : Nat)
         -----------------
      -> (x * y) ≡ (y * x)
comm-* x zero rewrite zero-* x = refl zero
comm-* x (succ y)
  rewrite comm-* x y
  | succ-distribute-* y x = refl (x + (y * x))

-- properties of + *

-- * distribute over + from right
distr-right-*+ : (x y z : Nat)
                 -----------------------------------
              -> (x * (y + z)) ≡ ((x * y) + (x * z))
distr-right-*+ x y zero = refl (x * y)
distr-right-*+ x y (succ z)
  rewrite distr-right-*+ x y z
  | assocRL-+ (x * y) x (x * z)
  | comm-+ (x * y) x
  | assocLR-+ x (x * y) (x * z) = refl (x + ((x * y) + (x * z)))

distr-left-*+ : (x y z : Nat)
                -----------------------------------
             -> ((x + y) * z) ≡ ((x * z) + (y * z))
distr-left-*+ x y z
  rewrite comm-* (x + y) z
  | distr-right-*+ z x y
  | comm-* z x
  | comm-* z y = refl ((x * z) + (y * z))

assocLR-* : (x y z : Nat)
            -----------------------------
         -> ((x * y) * z) ≡ (x * (y * z))
assocLR-* x y zero = refl zero
assocLR-* x y (succ z)
  rewrite assocLR-* x y z
  | distr-right-*+ x y (y * z) = refl ((x * y) + (x * (y * z)))

assocRL-* : (x y z : Nat)
            -----------------------------
         -> (x * (y * z)) ≡ ((x * y) * z)
assocRL-* a b c = ≡-comm (assocLR-* a b c)

-- observable equality of natural numbers
observable-=-Nat : Nat -> Nat -> Type
observable-=-Nat 0        0        = One
observable-=-Nat 0        (succ m) = Zero
observable-=-Nat (succ n) 0        = Zero
observable-=-Nat (succ n) (succ m) = observable-=-Nat n m

-- {-# BUILTIN NATEQUALS observable-=-Nat #-}

observable-=-Nat-refl : forall {n m : Nat}
  -> observable-=-Nat n m
  -> observable-=-Nat m n
observable-=-Nat-refl {zero} {zero} p     = p
observable-=-Nat-refl {succ n} {succ m} p = observable-=-Nat-refl {n} {m} p

{-
Robinson arithmetic axioms =
  Peano arithmetic axioms +
  n=0 or exists k. succ k = n
-}

robinson-axiom : (n : Nat) -> (n ≡ zero) \/ (Σ k :: Nat , (succ k ≡ n))
robinson-axiom zero = left (refl zero)
robinson-axiom (succ n) = right (n , refl (succ n))
