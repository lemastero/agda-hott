{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.These where

open import TypeTheory.Universes using (Type; 𝑢)
open import TypeTheory.SimpleTypes using (id; _compose_)
open import HoTT.Identity-Types using (_≡_; refl)

data These (A : Type 𝑢)(B : Type 𝑢) : Type 𝑢 where
  This : A       -> These A B
  That : B       -> These A B
  Those : A -> B -> These A B

-- operations

bimap-These : {A B AA BB : Type 𝑢} -> (A -> AA) -> (B -> BB) -> These A B -> These AA BB
bimap-These f g (This a) = This (f a)
bimap-These f g (That b) = That (g b)
bimap-These f g (Those a b) = Those (f a) (g b)

-- properties

bimap-These-id : {A : Type 𝑢} (fa : These A A) -> bimap-These id id fa ≡ fa
bimap-These-id (This a)      = refl (This a)
bimap-These-id (That a)      = refl (That a)
bimap-These-id (Those a1 a2) = refl (Those a1 a2)

bimap-These-compose : {A1 A2 A3 B1 B2 B3 : Type 𝑢} (f1 : A1 -> A2) (f2 : A2 -> A3)
    (g1 : B1 -> B2) (g2 : B2 -> B3) (fa : These A1 B1) ->
    bimap-These (f2 compose f1) (g2 compose g1) fa ≡
    bimap-These f2 g2 (bimap-These f1 g1 fa)
bimap-These-compose f1 f2 g1 g2 (This x) = refl (This (f2 (f1 x)))
bimap-These-compose f1 f2 g1 g2 (That x) = refl (That (g2 (g1 x)))
bimap-These-compose f1 f2 g1 g2 (Those x x1) = refl (Those (f2 (f1 x)) (g2 (g1 x1)))
