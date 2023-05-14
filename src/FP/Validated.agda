{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.Validated where

open import TypeTheory.Universes using (Type; 𝑢)
open import TypeTheory.SimpleTypes using (id; _compose_)
open import HoTT.Identity-Types using (_≡_; refl)

data Validated (A : Type 𝑢)(E : Type 𝑢) : Type 𝑢 where
  Success : A -> Validated A E
  Error   : E -> Validated A E

-- operations

map-Validated : {A B E : Type 𝑢} -> (A -> B) -> Validated A E -> Validated B E
map-Validated f (Success x) = Success (f x)
map-Validated f (Error x)   = Error x

bimap-Validated : {A B E F : Type 𝑢} -> (A -> B) -> (E -> F) -> Validated A E -> Validated B F
bimap-Validated f g (Success x) = Success (f x)
bimap-Validated f g (Error x)   = Error (g x)

-- properties of bimap-Validated

-- properties of bimap-Validated

Validated-bimap-id : {A : Type 𝑢} (fa : Validated A A)
            ->  bimap-Validated id id fa ≡ fa
Validated-bimap-id (Success x) = refl (Success x)
Validated-bimap-id (Error x)   = refl (Error x)

Validated-map-compose : {A1 A2 A3 B1 B2 B3 : Type 𝑢}
                 -> (f1 : A1 -> A2)
                 -> (f2 : A2 -> A3)
                 -> (g1 : B1 -> B2)
                 -> (g2 : B2 -> B3)
                 -> (fa : Validated A1 B1)
                 -> bimap-Validated (f2 compose f1) (g2 compose g1) fa ≡
                   bimap-Validated f2 g2 (bimap-Validated f1 g1 fa)
Validated-map-compose f1 f2 g1 g2 (Success x) = refl (Success (f2 (f1 x)))
Validated-map-compose f1 f2 g1 g2 (Error x)   = refl (Error (g2 (g1 x)))
