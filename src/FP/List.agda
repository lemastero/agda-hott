{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.List where

open import TypeTheory.Universes using (Type; 𝑢)
open import HoTT.Identity-Types using (refl; _≡_; ≡-sym)
open import TypeTheory.SimpleTypes using (id; _compose_)

data List (X : Type 𝑢) : Type 𝑢 where
  []     : List X
  _cons_ : X -> List X -> List X

infixr 4 _cons_

head : {X : Type 𝑢} -> X -> List X -> X
head d []          = d
head d (x cons xs) = x

tail : {X : Type 𝑢} -> List X -> List X
tail []          = []
tail (x cons xs) = xs

-- list concatenation
_concat_ : {X : Type 𝑢} -> List X -> List X -> List X
xs concat []          = xs
xs concat (x cons ys) = x cons (xs concat ys)

take : {X : Type 𝑢} -> List X -> List X
take []          = []
take (x cons xs) = x cons take xs

list :  {X : Type 𝑢} -> X -> List X
list x = x cons []

-- List apply
_<*>_ : forall {X Y : Type 𝑢} -> List (X -> Y) -> List X -> List Y
xs          <*> []          = []
[]          <*> (x cons xs) = []
(f cons fs) <*> (x cons xs) = (f x) cons (fs <*> xs)

-- List map
map-List : {X Y : Type 𝑢} -> (X -> Y) -> List X -> List Y
map-List f []           = []
map-List f (x cons xs) = (f x) cons map-List f xs

flatMap-List : {A B : Type 𝑢} -> (A -> List B) -> List A -> List B
flatMap-List f []          = []
flatMap-List f (x cons xs) = (f x) concat (flatMap-List f xs)

-- concat properties

concat-nil : {X : Type} (xs : List X) -> (xs concat []) ≡ xs
concat-nil = refl

nil-concat : {X : Type} (xs : List X) -> ([] concat xs) ≡ xs
nil-concat []          = refl []
nil-concat (x cons xs) rewrite nil-concat xs = refl (x cons xs)

concat-assoc : {X : Type} (xs ys zs : List X) ->
      ((xs concat ys) concat zs) ≡ (xs concat (ys concat zs))
concat-assoc xs ys []          = refl (xs concat ys)
concat-assoc xs ys (x cons zs)
  rewrite concat-assoc xs ys zs = refl (x cons (xs concat (ys concat zs)))

concat-assocLR : {X : Type} (xs ys zs : List X) ->
        (xs concat (ys concat zs)) ≡ ((xs concat ys) concat zs)
concat-assocLR xs ys zs = ≡-sym (concat-assoc xs ys zs)

-- map properties

map-id : {A : Type 𝑢} (fa : List A) -> map-List id fa ≡ fa
map-id []          = refl []
map-id (x cons xs) rewrite map-id xs = refl (x cons xs)

map-compose : {A B C : Type 𝑢} (f : A -> B) (g : B -> C) (fa : List A) ->
    map-List (g compose f) fa ≡ map-List g (map-List f fa)
map-compose f g []          = refl []
map-compose f g (x cons xs)
  rewrite map-compose f g xs =
  refl (g (f x) cons map-List g (map-List f xs))
