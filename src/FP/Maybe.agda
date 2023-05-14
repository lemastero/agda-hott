{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.Maybe where

open import TypeTheory.Universes using (Type; 𝑢)
open import TypeTheory.SimpleTypes using (id; _compose_)
open import HoTT.Identity-Types using (_≡_; refl)

data Maybe (A : Type 𝑢) : Type 𝑢 where
  Just : (x : A) -> Maybe A
  None :            Maybe A

-- operations

map-Maybe : {A B : Type 𝑢} -> (A -> B) -> Maybe A -> Maybe B
map-Maybe f (Just a) = Just (f a)
map-Maybe f None     = None

flatMap-Maybe : {A B : Type 𝑢} -> Maybe A -> (A -> Maybe B) -> Maybe B
flatMap-Maybe (Just a) f = f a
flatMap-Maybe None     f = None

-- propos of map

maybe-map-id : {A : Type 𝑢} (fa : Maybe A)
            -> map-Maybe id fa ≡ fa
maybe-map-id (Just a) = refl (Just a)
maybe-map-id None     = refl None

maybe-map-compose : {A B C : Type 𝑢}
                 -> (f : A -> B)
                 -> (g : B -> C)
                 -> (fa : Maybe A)
                 -> map-Maybe (g compose f) fa ≡ map-Maybe g (map-Maybe f fa)
maybe-map-compose f g (Just x) = refl (Just (g (f x)))
maybe-map-compose f g None     = refl None

-- propos of flatMap

maybe-flatMap-just-f : {A B : Type 𝑢} (a : A) (f : A -> Maybe B)
            -> flatMap-Maybe (Just a) f ≡ f a
maybe-flatMap-just-f a fab = refl (fab a)

maybe-flatMap-f-just : {A : Type 𝑢} (fa : Maybe A) -> flatMap-Maybe fa Just ≡ fa
maybe-flatMap-f-just (Just x) = refl (Just x)
maybe-flatMap-f-just None     = refl None

maybe-flatMap-compose : {A B C : Type 𝑢}
  -> (f : A -> Maybe B)
  -> (g : B -> Maybe C)
  -> (fa : Maybe A)
  -> flatMap-Maybe (flatMap-Maybe fa f) g ≡
     flatMap-Maybe fa (\ x -> flatMap-Maybe (f x) g)
maybe-flatMap-compose fab fbc (Just x) = refl (flatMap-Maybe (fab x) fbc)
maybe-flatMap-compose fab fbc None = refl None
