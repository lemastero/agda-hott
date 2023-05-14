{-# OPTIONS --without-K --exact-split --safe #-}

module TypeTheory.Negation where

open import TypeTheory.Universes
open import TypeTheory.SimpleTypes
open import TypeTheory.Product
open import TypeTheory.Sum
open import HoTT.Identity-Types
open import TypeTheory.LogicalEquiv

--------------------------------------
-- logical negation

not : Type 𝑢 -> Type 𝑢
not X = X -> Zero

-- double negation
not-not : Type 𝑢 -> Type 𝑢
not-not A = not (not A) -- (A -> 0) -> 0

-- tripple negation
not-not-not : Type 𝑢 -> Type 𝑢
not-not-not A = not (not-not A)

-- double negation introduction A => ¬¬A
not-not-intro : {A : Type 𝑢} -> A -> not-not A
not-not-intro a absurdA = absurdA a

-- if we have function A->B and B is empty B -> 0
-- then A is empty A -> 0
contrapositive : {A : Type 𝑢} {B : Type 𝑤}
                 -> (A -> B)
                 -> not B -> not A
contrapositive f b->0 a = b->0 (f a)

-- absurdity of absurdity of absurdity is absurdity
not-not-not-A-imply-not-A : {A : Type 𝑢}
                         -> not (not (not A))
                         -> not A
not-not-not-A-imply-not-A nnna = contrapositive not-not-intro nnna

not-not-not-intro : {A : Type 𝑢}
                 -> not A
                 -> not (not (not A))
not-not-not-intro nA = not-not-intro nA

absurdity^3-is-absurdity : {A : Type 𝑢}
                           -> not (not (not A)) <=> not A
absurdity^3-is-absurdity {u} {X} =
  ( firstly ,, secondly )
  where
   firstly : not (not (not X)) -> not X
   firstly = not-not-not-A-imply-not-A
   secondly : not X -> not (not (not X))
   secondly = not-not-not-intro

1-is-not-empty : not (is-empty One)
1-is-not-empty f = f <>

----------------------------------
-- negation of Identity types
-- x1 ≡ x2 -> 0
-- inequality "x1 is not equal to x2 in type X"
_≡/_ : {X : Type 𝑢} -> X -> X -> Type 𝑢
x1 ≡/ x2 = not (x1 ≡ x2)

-- swap
≡/-sym : {A : Type 𝑢} {x y : A} -> x ≡/ y -> y ≡/ x
≡/-sym  {U} {A} {x} {y} x-no≡-y = \ y≡x -> x-no≡-y (≡-swap (y≡x)) -- (y ≡ x) -> Zero

{-- not transitive a ≡/ b, b ≡/ a but a ≡ a
≡/-not-trans : {A : Type 𝑢} {x y z : A} -> not ( x ≡/ y -> y ≡/ z -> x ≡/ z )
≡/-not-trans a = {!   !}
-}

One-is-not-Zero : One ≡/ Zero
One-is-not-Zero 1=0 = ≡->Fun 1=0 <>

right-fails-gives-left-holds : {P : Type 𝑢} {Q : Type 𝑤}
                          -> (P + Q) -> (not Q) -> P
right-fails-gives-left-holds (left p) u = p
right-fails-gives-left-holds (right q) u = absurd _ (u q)
