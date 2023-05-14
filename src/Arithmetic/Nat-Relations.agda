{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module Arithmetic.Nat-Relations where

open import TypeTheory.Universes using (Type)
open import TypeTheory.SimpleTypes using (Zero; One; <>; Nat; zero; succ)
open import TypeTheory.Negation using (not)
open import TypeTheory.Sum renaming (_+_ to _\/_)
open import HoTT.Identity-Types using (_≡_; refl; cong)

{-
axioms for <
  x < y <=> exists z (succ z + x = y)
  not (x < 0)
  x < succ y <=> (x < y or x = y)
  x < y or x = y or y < x

Natural numbers axioms using ordered semiring
  x < y and y < z => x < z         < is transitive
  not (x < x)                      < is irreflexivie
  x < y or x = y or y < x          ordering trichotomy
  x < y  => x + z < y + z          ordering is preserved under addition
  0 < z and x < y => x * z < y * z ordering is preserved under multiplication
  x < y <=> exists z. (x + z = y)
  0 < 1 and (x > 0 => x >= 1)     0 is different than 1 and there is not element between them
  x >= 0
-}

{- <= relation -}

_<=_ : Nat -> Nat -> Type
zero     <= n        = One
(succ x) <= zero     = Zero
(succ x) <= (succ y) = x <= y

refl-<= : (n : Nat)
          ---------
       -> n <= n
refl-<= 0 = <>
refl-<= (succ x) = refl-<= x

trans-<= : (x y z : Nat)
        -> x <= y -> y <= z
           -----------------
        -> x <= z
trans-<= 0 y z x<=y y<=z = <>
trans-<= (succ x) (succ y) (succ z) x<=y y<=z = trans-<= x y z x<=y y<=z

<=-distrib-succ : (x y : Nat)
        -> x <= y
        --------------------
        -> succ x <= succ y
<=-distrib-succ zero     zero     <>   = <>
<=-distrib-succ zero     (succ y) x<=y = <>
<=-distrib-succ (succ x) (succ y) x<=y = x<=y

succ-distrib-<= : (x y : Nat)
        -> succ x <= succ y
        --------------------
        -> x <= y
succ-distrib-<= x y p = p

total<= : (m n : Nat)
       -> (m <= n) \/ (n <= m)
total<= m        zero     = right <>
total<= zero     (succ n) = left <>
total<= (succ m) (succ n) = total<= m n

antisymmetric<= : (m n : Nat)
               -> (m <= n) -> (n <= m)
                  -----------------
               -> m ≡ n
antisymmetric<= zero     zero     m<=n n<=m = refl zero
antisymmetric<= zero     (succ n) m<=n ()
antisymmetric<= (succ n) zero     ()   n<=m
antisymmetric<= (succ m) (succ n) m<=n n<=m =
  cong succ (antisymmetric<= m n m<=n n<=m)

{- < relation -}

_<_ : Nat -> Nat -> Type
n        < zero     = Zero
zero     < (succ n) = One
(succ x) < (succ y) = x < y

trans-< : (x y z : Nat)
       -> x < y -> y < z
          --------------
       -> x < z
trans-< zero (succ y) (succ z) <> y<z      = <>
trans-< (succ x) (succ y) (succ z) x<y y<z =
  trans-< x y z x<y y<z

irreflexive< : (n : Nat) -> not (n < n)
irreflexive< zero     ()
irreflexive< (succ n) p = irreflexive< n p

asymmetric< : (n m : Nat) -> n < m -> not (m < n)
asymmetric< zero     (succ m) n<m ()
asymmetric< (succ n) zero     ()  m<n
asymmetric< (succ n) (succ m) n<m m<n = asymmetric< n m n<m m<n

{- >= relation -}

_>=_ : Nat -> Nat -> Type
x       >= 0         = One
0       >= (succ y)  = Zero
(succ x) >= (succ y) = x >= y

refl->= : (n : Nat) -> n >= n
refl->= 0        = <>
refl->= (succ n) = refl->= n

trans->= : (x y z : Nat)
        -> x >= y -> y >= z
           ----------------
        -> x >= z
trans->= x y 0 x>=y y>=z = <>
trans->= (succ x) (succ y) (succ z) x>=y y>=z =
  trans->= x y z x>=y y>=z

total>= : (m n : Nat)
      -> (m >= n) \/ (n >= m)
total>= zero     n        = right <>
total>= (succ m) zero     = left <>
total>= (succ m) (succ n) = total>= m n

antisymmetric>= : (m n : Nat)
               -> m >= n -> n >= m
                  -----------------
               -> m ≡ n
antisymmetric>= zero     zero     m>=n n>=m = refl zero
antisymmetric>= zero     (succ n) ()   n>=m
antisymmetric>= (succ m) zero     m>=n ()
antisymmetric>= (succ m) (succ n) m>=n n>=m = cong succ (antisymmetric>= m n m>=n n>=m)

{- > relation -}

_>_ : Nat -> Nat -> Type
0        > n        = Zero
(succ x) > 0        = One
(succ x) > (succ y) = x > y

trans-> : (x y z : Nat)
       -> (x > y) -> (y > z)
          ------------------
       -> x > z
trans-> (succ x) (succ y) zero     x>y <>  = <>
trans-> (succ x) (succ y) (succ z) x>y y>z = trans-> x y z x>y y>z

irreflexive> : (n : Nat) -> not (n > n)
irreflexive> zero     ()
irreflexive> (succ n) p = irreflexive> n p

asymmetric> : (n m : Nat) -> n > m -> not (m > n)
asymmetric> zero     (succ m) ()  m>n
asymmetric> (succ n) zero     n>m ()
asymmetric> (succ n) (succ m) n>m m>n = asymmetric> n m n>m m>n
