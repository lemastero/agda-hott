{-# OPTIONS --without-K --exact-split --safe #-}

module TypeTheory.Sum where

open import TypeTheory.Universes
open import TypeTheory.SimpleTypes
open import HoTT.Identity-Types using (_≡_; refl)

-- binary sum type / either / coproduct / disjoint union / or
data _+_ (X : Type 𝑢) (Y : Type 𝑤) : Type (𝑢 umax 𝑤) where
 left  : X -> X + Y
 right : Y -> X + Y

infixr 20 _+_

+elim : {X : Type 𝑢} {Y : Type 𝑤} (P : X + Y -> Type 𝑧)
 -> ((x : X) -> P (left  x))   -- base case left (bracket for easier pattern matching)
 -> ((y : Y) -> P (right y))   -- base case right (bracket for easier pattern matching)
                               -- no inductive case
 -> (z : X + Y) -> P z         -- property P holds for all elements of X + Y
+elim P f _ (left x) = f x
+elim P _ g (right y) = g y

+rec : {X : Type 𝑢} {Y : Type 𝑤} (P : Type 𝑧)
 -> (X -> P)
 -> (Y -> P)
 -> (X + Y) -> P
+rec P xp yp xy = +elim
     (\ XY -> P) -- in +-induction P is dependent type so fake it
     xp yp xy    -- could skip those

+right-id : {A : Type 𝑢} -> A + ZeroL {𝑢} -> A
+right-id (left a) = a

+id-right : {A : Type 𝑢} -> A -> A + ZeroL {𝑢}
+id-right = left

+left-id : {A : Type 𝑢} -> ZeroL {𝑢} + A -> A
+left-id (right a) = a

+id-left : {A : Type 𝑢} -> A -> ZeroL {𝑢} + A
+id-left = right

+comm : {A B : Type 𝑢} -> A + B -> B + A
+comm (left a) = right a
+comm (right b) = left b

+assocLR : {A B C : Type 𝑢} -> (A + B) + C -> A + (B + C)
+assocLR (left (left a)) = left a
+assocLR (left (right b)) = right (left b)
+assocLR (right c) = right (right c)

+assocRL : {A B C : Type 𝑢} -> A + (B + C) -> (A + B) + C
+assocRL (left a) = left (left a)
+assocRL (right (left b)) = left (right b)
+assocRL (right (right c)) = right c

bimap+ : {A B AA BB : Type 𝑢}
      -> (A -> AA)
      -> (B -> BB)
      -> A + B -> AA + BB
bimap+ f g (left x)  = left (f x)
bimap+ f g (right x) = right (g x)

bimap+id : {A : Type 𝑢} (fa : A + A) -> bimap+ id id fa ≡ fa
bimap+id (left x)  = refl (left x)
bimap+id (right x) = refl (right x)

bimap+compose : {A1 A2 A3 B1 B2 B3 : Type 𝑢} (f1 : A1 -> A2) (f2 : A2 -> A3)
      (g1 : B1 -> B2) (g2 : B2 -> B3) (fa : A1 + B1) ->
      bimap+ (f2 compose f1) (g2 compose g1) fa ≡
      bimap+ f2 g2 (bimap+ f1 g1 fa)
bimap+compose f1 f2 g1 g2 (left x)  = refl (left (f2 (f1 x)))
bimap+compose f1 f2 g1 g2 (right x) = refl (right (g2 (g1 x)))
