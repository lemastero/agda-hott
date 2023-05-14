{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.Vec where

open import TypeTheory.Universes using (Type; 𝑢)
open import TypeTheory.SimpleTypes using (Nat; succ; zero; id; _compose_)
open import Arithmetic.Nat-Peano using (_+_; _*_)
open import Arithmetic.Nat-Relations using (_>=_; refl->=)
open import HoTT.Identity-Types using (refl; _≡_)

data Vec (X : Type 𝑢) : Nat -> Type 𝑢 where
  []   : Vec X 0
  _vcons_ : {n : Nat} -> X -> Vec X n -> Vec X (succ n)

infixr 4 _vcons_

vHead : {X : Type 𝑢}{n : Nat} -> Vec X (succ n) -> X
vHead (x vcons xs) = x

vTail : {X : Type 𝑢}{n : Nat} -> Vec X (succ n) -> Vec X n
vTail (x vcons xs) = xs

_+V_ : {X : Type 𝑢}{m n : Nat} -> Vec X m -> Vec X n -> Vec X (m + n)
xs +V [] = xs
xs +V (x vcons ys) = x vcons (xs +V ys)

-- take n elemenf from front of the bector
vTake : {X : Type 𝑢}(m n : Nat) -> m >= n -> Vec X m -> Vec X n
vTake m        0        m>=n xs           = []
vTake (succ m) (succ n) m>=n (x vcons xs) = x vcons vTake m n m>=n xs


VTakeId : (n : Nat){X : Type}(xs : Vec X n)
       -> (vTake n n (refl->= n) xs) ≡ xs
VTakeId 0        []          = refl []
VTakeId (succ n) (x vcons v) rewrite VTakeId n v =
  refl (x vcons v)

-- Vector return
vec : {n : Nat} {X : Type 𝑢} -> X -> Vec X n
vec {u} {zero}   x = []
vec {u} {succ n} x = x vcons vec x

-- Vector apply
_<*>_ : {n : Nat} {X Y : Type 𝑢} -> Vec (X -> Y) n -> Vec X n -> Vec Y n
[]           <*> []            = []
(f vcons fs) <*> (x vcons xs) = (f x) vcons (fs <*> xs)

-- Vector map
vMap : {n : Nat}{X Y : Type 𝑢} -> (X -> Y) -> Vec X n -> Vec Y n
vMap f []           = []
vMap f (x vcons xs) = (f x) vcons vMap f xs

vecFlatMap : {n m : Nat}{A B : Type 𝑢} -> (A -> Vec B n) -> Vec A m -> Vec B (n * m)
vecFlatMap f []           = []
vecFlatMap f (x vcons xs) = f x +V (vecFlatMap f xs)

vecFlatten : {n m : Nat}{A : Type 𝑢} -> Vec (Vec A n) m -> Vec A (n * m)
vecFlatten []           = []
vecFlatten (x vcons xs) = x +V (vecFlatten xs)

vMap-id : (n : Nat)
       -> {A : Type 𝑢} (fa : Vec A n)
       -> vMap id fa ≡ fa
vMap-id zero []               = refl []
vMap-id (succ n) (x vcons xs)
  rewrite vMap-id n xs = refl (x vcons xs)

vMap-compose : (n : Nat) -> {A B C : Type 𝑢}
            -> (f : A -> B)
            -> (g : B -> C)
            -> (fa : Vec A n)
            -> vMap (g compose f) fa ≡ vMap g (vMap f fa)
vMap-compose zeri     f g []           = refl []
vMap-compose (succ n) f g (x vcons xs)
  rewrite vMap-compose n f g xs = refl (g (f x) vcons vMap g (vMap f xs))
