{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.SimplifiedCategories.Category where

open import TypeTheory.Universes using (Type; 𝑢; 𝑤; usuc; _umax_)
open import HoTT.Identity-Types using (_≡_)

record Category (Obj : Type 𝑢)(_=>_ : Obj -> Obj -> Type 𝑤) : Type (usuc (𝑢 umax 𝑤)) where
  field
    -- operations
    c-id : forall (A : Obj) -> (A => A)
    _c-andThen_ : forall {A B C : Obj}  -- easier for chasing diagrams
          -> (A => B)
          -> (B => C)
          -> (A => C)
    -- laws
    C-left-identity : forall {A B : Obj}
          -> (f : A => B)
          -> c-id A c-andThen f ≡ f
    C-right-identity : forall {A B : Obj}
          -> (fa : A => B)
          -> fa c-andThen c-id B ≡ fa
    C-associativity : forall {A B C D : Obj}
          -> (f : (A => B))
          -> (g : (B => C))
          -> (h : (C => D))
          -> f c-andThen (g c-andThen h) ≡ (f c-andThen g) c-andThen h
  _c-compose_ : forall {A B C : Obj}
      -> (B => C)
      -> (A => B)
      -> (A => C)
  f c-compose g = g c-andThen f
  Hom : Obj -> Obj -> Type 𝑤
  Hom A B = A => B
