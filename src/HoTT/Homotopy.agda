{-# OPTIONS --without-K --exact-split --safe #-}

module HoTT.Homotopy where

open import TypeTheory.Universes
open import TypeTheory.Dependent-Types
open import HoTT.Identity-Types

-- pointwise equality of functions
-- homotopy
_~_ : {A : Type 𝑢} {B : A -> Type 𝑤 }
    -> ( f : ( (a : A) -> B a ) ) -- (f : Pi B)
    -> ( g : ( (a : A) -> B a ) ) -- (g : Pi B)
    -> Type (𝑢 umax 𝑤)
f ~ g = forall x -> f x ≡ g x

infix 0 _~_

-- propertis of homotopies

~reflexivity : {A : Type 𝑢} {B : A -> Type 𝑤 }
     -> ( f : (a : A) -> B a )
     -> f ~ f
~reflexivity f a = refl (f a)

~symmetry : {A : Type 𝑢} {B : A -> Type 𝑤 }
    -> ( f : (a : A) -> B a )
    -> ( g : (a : A) -> B a )
    -> (f ~ g)
    -> (g ~ f)
~symmetry f g f~g x = ≡-swap (f~g x)

~transitivity : {A : Type 𝑢} {B : A -> Type 𝑤 }
    -> ( f : (a : A) -> B a )
    -> ( g : (a : A) -> B a )
    -> ( h : (a : A) -> B a )
    -> (f ~ g) -> (g ~ h)
    -> (f ~ h)
~transitivity f g h f~g g~h a = (f~g a) ∙ (g~h a)

-- inverse of homotopy
-- swap of homotopy
~inv : {A : Type 𝑢} {B : A -> Type 𝑤 }
    -> ( f : ( (a : A) -> B a ) )
    -> ( g : ( (a : A) -> B a ) )
    -> (f ~ g) -> (g ~ f)
~inv = ~symmetry

≡to~ : {X Y : Set} (f : X -> Y) (g : X -> Y) -> (f ≡ g) -> f ~ g
≡to~ f f (refl f) x = refl (f x)

-- homotopy of homotopies
_≈_ : {A : Type 𝑢} {B : A -> Type 𝑤 }
    -> { f : ( (a : A) -> B a ) }
    -> { g : ( (a : A) -> B a ) }
    -> ( H : (f ~ g) )
    -> ( K : (f ~ g) )
    -> Type (𝑢 umax 𝑤)
H ≈ K = forall x -> H x ≡ K x

-- whiskering to left
--            f
--        ___________
--        |   ||    |
--    k   |   ||    \/
-- D ---> A   || H   B
--        |   ||    /\
--        |   ||    |
--         ----------
--            g
---------------------
_~≈_ : {A : Type 𝑢} {B : A -> Type 𝑤 }
       {D : Type 𝑧 }
    -> { f : ( (a : A) -> B a ) }
    -> { g : ( (a : A) -> B a ) }
    -> ( H : (f ~ g) )
    -> ( k : (D -> A) )
    -> (f Π-compose1 k) ~ (g Π-compose1 k)
(H ~≈ k) = \ y -> H (k y)

-- whiskering to right
--       f
--   ___________
--   |   ||    |
--   |   ||    \/   h
--   A   || H  B -------> C
--   |   ||    /\
--   |   ||    |
--   ----------
--       g
---------------------
