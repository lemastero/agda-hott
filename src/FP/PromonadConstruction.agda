{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.PromonadConstruction where

open import TypeTheory.Universes using (Type; 𝑢; usuc; Universe)
open import TypeTheory.SimpleTypes using (Nat; succ; zero; id; _compose_)
open import Arithmetic.Nat-Peano using (_+_; _*_)
open import Arithmetic.Nat-Relations using (_>=_)
open import HoTT.Identity-Types using (refl; _≡_)
open import FP.Types using (Function)


-- TODO Theory of Promonads: https://math.stackexchange.com/questions/372380/theory-of-promonads
-- TODO https://arxiv.org/pdf/2001.07488.pdf Definition 4.8
-- TODO https://arxiv.org/pdf/2001.08045.pdf Definition 2.3.1
record Promonad (Morph : Type 𝑢 -> Type 𝑢 -> Type 𝑢) : Type (usuc 𝑢) where
  field
    Unit : forall {A : Type 𝑢} -> Morph A A
    Multi : forall {A B C : Type 𝑢} -> Morph A B -> Morph B C -> Morph A C

record PromonadLowering (F : Type 𝑢 -> Type 𝑢) : Type (usuc 𝑢) where
  field
    -- type
    Morph : Type 𝑢 -> Type 𝑢 -> Type 𝑢 -- uses F to list function into profunctor e.g. (A -> F B) -> Morph A B
    isPromonad : Promonad Morph
    -- operation
    run : forall {A B : Type 𝑢} -> (f : Morph A B) -> F A -> F B

  open Promonad isPromonad

  -- derived definition of laws
  identityLaw : forall {A : Type 𝑢}
             -> (fa : F A)
             -> Type 𝑢
  identityLaw fa = run Unit fa ≡ fa
  composeLaw  : forall {A B C : Type 𝑢}
             -> (fa : F A)
             -> (f : Morph A B)
             -> (g : Morph B C)
             -> Type 𝑢
  composeLaw fa f g = (run g (run f fa)) ≡ run (Multi f g) fa

-- TODO Functoriality
-- TODO In what way it is Monad (?)
-- TODO can we show somehow it is Applicative (study B. Milewski 3 equivalent definitions)

-- TODO WIP Notions of computations as Promonad
