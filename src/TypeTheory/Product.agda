{-# OPTIONS --without-K --exact-split --safe #-}

module TypeTheory.Product where

open import TypeTheory.Universes using (Type; 𝑢; 𝑤; _umax_)
open import TypeTheory.SimpleTypes
open import HoTT.Identity-Types using (_≡_; refl)

-- binary product / pair / tuple
record _×_ (S : Type 𝑢)(T : Type 𝑤) : Type (𝑢 umax 𝑤)  where
  constructor _,,_
  field
    fst : S
    snd : T

elim-× : {A : Type 𝑢}{B : Type 𝑤}
    -> (P : (A × B) -> Type)
    -> ( (a : A) -> (b : B) -> P (a ,, b) )
    --------------------------
    -> (ab : A × B) -> P ab
elim-× P f (x ,, y) = f x y

×right-id : {A : Type 𝑢} -> (A × OneL {𝑢}) -> A
×right-id (a ,, _) = a

×id-right : {A : Type 𝑢} -> A -> (A × OneL {𝑢})
×id-right a = (a ,, <>)

×left-id : {A : Type 𝑢} -> OneL {𝑢} × A -> A
×left-id (_ ,, a) = a

×id-left : {A : Type 𝑢} -> A -> OneL {𝑢} × A
×id-left a = (<> ,, a)

×-comm : {A : Type 𝑢}{B : Type 𝑢} -> A × B -> B × A
×-comm (a ,, b) = (b ,, a)

×assocLR : {A B C : Type 𝑢} -> (A × B) × C -> A × (B × C)
×assocLR ((a ,, b) ,, c) = (a ,, (b ,, c))

×assocRL : {A B C : Type 𝑢} -> A × (B × C) -> (A × B) × C
×assocRL (a ,, (b ,, c)) = ((a ,, b) ,, c)

×-diag : {A : Type 𝑢}
        -> A
        -> (A × A)
×-diag x = (x ,, x)

×bimap : {A B AA BB : Type 𝑢} ->
      (A -> AA) -> (B -> BB) -> A × B -> AA × BB
×bimap f g (a ,, b) = f a ,, g b

×bimap-id : {A : Type 𝑢} (fa : A × A) -> ×bimap id id fa ≡ fa
×bimap-id (a1 ,, a2) = refl (a1 ,, a2)

×bimap-compose : {A1 A2 A3 B1 B2 B3 : Type 𝑢} (f1 : A1 -> A2) (f2 : A2 -> A3)
    (g1 : B1 -> B2) (g2 : B2 -> B3) (fa : A1 × B1) ->
    ×bimap (f2 compose f1) (g2 compose g1) fa ≡
    ×bimap f2 g2 (×bimap f1 g1 fa)
×bimap-compose f1 f2 g1 g2 (a ,, b) = refl ( (f2 compose f1) a ,, (g2 compose g1) b)
