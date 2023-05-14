{-# OPTIONS --without-K --exact-split --safe #-}

module HoTT.Homotopy-Levels where

open import TypeTheory.Universes
open import TypeTheory.Dependent-Types
open import TypeTheory.SimpleTypes
open import HoTT.Identity-Types
open import TypeTheory.Negation

-- groupoid structure of types
-- is-contr    -2 types   singleton                    -2 groupoids   contractible space
-- is-prop     -1 types   subsingletons, propositions  -1 groupoids   has at most 1 point up to paths
-- is-set       0 types                                0 groupoids    space whos path space is propositions
-- is-type      1 types                                1 groupoids    space whose path space is set
-- is-category  2 types                                2 groupoids
-- ...

-- there is designated c : X
-- that is identified with each x : X
is-contractible : Type 𝑢 -> Type 𝑢
is-contractible X = Σ c :: X , ((x : X) -> c ≡ x)

-- element c : X is center of contraction
is-center : (X : Type 𝑢) -> X -> Type 𝑢
is-center X c = (x : X) -> c ≡ x

is-proposition : Type 𝑢 -> Type 𝑢
is-proposition X = forall (x y : X) -> x ≡ y

-- type is set if there is at most 1 way for any two of its elements to be equal
is-set : Type 𝑢 -> Type 𝑢
is-set X = (x y : X) -> is-proposition (x ≡ y)

is-groupoid : Type 𝑢 -> Type 𝑢
is-groupoid X = (x y : X) -> is-set (x ≡ y)

-- examples

1-is-contractible : is-contractible One
1-is-contractible = <> , 1-elim (\x -> <> ≡ x) (refl <>)

0-is-proposition : is-proposition Zero
0-is-proposition x y = absurd (x ≡ y) x

1-is-proposition : is-proposition One
1-is-proposition <> <> = refl <>

-- other names

-- exactly 1 point up to paths
is-singleton : Type 𝑢 -> Type 𝑢
is-singleton X = is-contractible X

-- has at most 1 element up to paths
-- (any 2 of its elements are equal or identified)
is-subsingleton : Type 𝑢 -> Type 𝑢
is-subsingleton X = is-proposition X

-- Univalent Excluded Middle

Univalent-EM : forall 𝑢 -> Type (usuc 𝑢)
Univalent-EM U = (X : Type U) -> is-proposition X -> X × (not X)
