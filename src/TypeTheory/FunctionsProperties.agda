{-# OPTIONS --without-K --exact-split --safe #-}

module TypeTheory.FunctionsProperties where

open import TypeTheory.Universes
open import TypeTheory.SimpleTypes using (_compose_; _andThen_; id)
open import HoTT.Identity-Types using (refl; _≡_)

compose3 : {A B C D : Type 𝑢}
    -> (A -> B) -> (B -> C) -> (C -> D)
    -> (A -> D)
compose3 = \ f g h -> h compose (g compose f)

function-dimap-id : {A : Type 𝑢}
         -> (f : A -> A)
         -> ((id compose f) compose id) ≡ f
function-dimap-id = refl

compose-id : {A B : Type 𝑢}
          -> (f : A -> B)
          -> (f compose id) ≡ f
compose-id = refl

id-compose : {A B : Type 𝑢}
          -> (f : A -> B)
          -> (id compose f) ≡ f
id-compose {A} {B} = refl

compose-assoc : {A B C D : Type 𝑢}
      -> (f : B -> A)
      -> (g : C -> B)
      -> (h : A -> D)
      -> (h compose (f compose g)) ≡ ((h compose f) compose g)
compose-assoc = \ f g h -> refl (h compose (f compose g))

andThen-assoc : {A B C D : Type}
      -> (f : A -> B)
      -> (g : B -> C)
      -> (h : C -> D)
      -> (f andThen (g andThen h)) ≡ ((f andThen g) andThen h)
andThen-assoc {A} {B} {C} {D} f g h = refl (f andThen (g andThen h))

compose-compose : {A B C D : Type 𝑢}
      -> (f : D -> B)
      -> (g : B -> C)
      -> (h : A -> D)
      -> ((g compose f) compose h) ≡ (g compose (f compose h))
compose-compose = \ f g h -> refl (g compose (f compose h))

function-dimap-compose : {A1 A2 A3 B1 B2 B3 : Type 𝑢}
    -> (f1 : A2 -> A1)
    -> (f2 : A3 -> A2)
    -> (g1 : B1 -> B2)
    -> (g2 : B2 -> B3)
    -> (fg : A1 -> B1)
    -> (((g2 compose g1) compose fg) compose (f1 compose f2))
       ≡
       ((g2 compose ((g1 compose fg) compose f1)) compose f2)
function-dimap-compose = \ f1 f2 g1 g2 fg -> refl (((g2 compose g1) compose fg) compose ((f1 compose f2)))
