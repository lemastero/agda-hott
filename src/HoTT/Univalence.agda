-- A self-contained, brief and complete formulation of Voevodsky’s Univalence Axiom
-- Martín Hötzel Escardó
-- https://arxiv.org/pdf/1803.02294.pdf

-- https://github.com/emilyriehl/721/blob/master/exercises8.agda
-- Emily Rhiel

-- Coq:   https://gist.github.com/JasonGross/c6745e6d3ffbab3ee7034988c1b5b904
-- Idris: https://github.com/jdolson/univalence-from-scratch/blob/master/Univalence.idr

{-# OPTIONS --without-K --exact-split --safe #-}

module HoTT.Univalence where

open import TypeTheory.Universes
open import TypeTheory.SimpleTypes using (id ; id')
open import TypeTheory.Product using (_×_ ; _,,_)
open import TypeTheory.Dependent-Types using (Σ ; _,_; _Π-compose1_)
open import HoTT.Identity-Types using (_≡_ ; refl)
open import HoTT.Homotopy using (_~_)

-- section (split surjection)
-- sec(f) := Σ (g : Y->X) , f . g ~ id(Y)
sec : {X : Type 𝑢}{Y : Type 𝑤}
   -> (X -> Y)
   -> Type (𝑢 umax 𝑤)
sec {X = X} {Y = Y} f = Σ \(g : Y -> X) -> (f Π-compose1 g) ~ id' Y

-- retraction  ret(f) := Σ (h : Y->X) , h . f ~ id(A)
retr : {X : Type 𝑢}{Y : Type 𝑤}
   -> (X -> Y)
   -> Type (𝑢 umax 𝑤)
retr {X = X} {Y = Y} f = Σ \(r : Y -> X) -> (r Π-compose1 f) ~ id' X

-- equivalence is-equiv(f) := sec(f) × ret(f)
is-equiv : {X : Type 𝑢}{Y : Type 𝑤}
   -> (X -> Y)
   -> Type (𝑢 umax 𝑤)
is-equiv f = sec(f) × retr(f)

-- identity function is equivalence
id-is-equiv : {X : Type 𝑢} -> is-equiv (id' X)
id-is-equiv = (id , refl) ,, (id , refl)

-- types are equivalent if every function between them is equivalence
_≃_ : (X : Type 𝑢)(Y : Type 𝑤)
   -> Type (𝑢 umax 𝑤)
X ≃ Y = Σ \(f : X -> Y) -> is-equiv f

-- identity equivalence
-- equivalence of types is reflexive
≃refl : {X : Type 𝑢} -> X ≃ X
≃refl {X = X} = id , id-is-equiv {X = X}

≡-to-≃ : (X Y : Type 𝑢) -> X ≡ Y -> X ≃ Y
≡-to-≃ X Y (refl X) = ≃refl

is-Univalent : (X Y : Type 𝑢) -> Type (usuc 𝑢)
is-Univalent X Y = is-equiv ( ≡-to-≃ X Y )
