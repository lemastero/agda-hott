{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.Abstractions.Monad where

open import TypeTheory.Universes using (Type; 𝑢; usuc; Universe)
open import HoTT.Identity-Types using (refl; _≡_)
open import FP.Abstractions.Applicative using (Applicative)
open import FP.Abstractions.Functor using (Functor)

record Monad (F : Type 𝑢 -> Type 𝑢) {{ _ : Functor F }} {{ _ : Applicative F }} : Type (usuc 𝑢) where
  field
    -- operations
    return : forall {A : Type 𝑢} -> A -> F A
    _>>=_  : forall {A B : Type 𝑢} -> F A -> (A -> F B) -> F B
    -- laws
    return-flatmap : forall {A B : Type 𝑢}
           -> (a : A)
           -> (f : A -> F B)
           -> return a >>= f ≡ f a
    flatmap-return : forall {A : Type 𝑢}
           -> (fa : F A)
           -> fa >>= return ≡ fa
    flatmap-compose : forall {A B C : Type 𝑢}
           -> (f : A -> F B)
           -> (g : B -> F C)
           -> (fa : F A)
           -> (fa >>= f) >>= g ≡ fa >>= (\ x -> f x >>= g)
  -- derived operations
  _>=>_ : {A B C : Type 𝑢} -> (B -> F C) -> (A -> F B) -> (A -> F C)
  (f >=> g) a = g a >>= f
