{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.Abstractions.Zifunctor where

open import TypeTheory.Universes using (Type; 𝑢; usuc; Universe)
open import TypeTheory.SimpleTypes using (OneL; <>; unit; id; _compose_)
open import HoTT.Identity-Types using (refl; _≡_)
open import FP.Types using (Function)
open import TypeTheory.Product using (_×_; ×bimap)
open import TypeTheory.Sum using (_+_; bimap+)

record Zifunctor (F : Type 𝑢 -> Type 𝑢 -> Type 𝑢 -> Type 𝑢) : Type (usuc 𝑢) where
  field
    -- operations
    zimap : forall {A B C AA BB CC : Type 𝑢}
        -> (AA -> A)
        -> (B -> BB)
        -> (C -> CC)
        -> F A B C -> F AA BB CC
    -- laws
    zimap-id : forall {A : Type 𝑢}
          -> (fa : F A A A)
          -> zimap id id id fa ≡ fa

    zimap-compose : forall {A1 A2 A3 B1 B2 B3 C1 C2 C3 : Type 𝑢}
          -> (f1 : (A2 -> A1))
          -> (f2 : (A3 -> A2))
          -> (g1 : (B1 -> B2))
          -> (g2 : (B2 -> B3))
          -> (h1 : (C1 -> C2))
          -> (h2 : (C2 -> C3))
          -> (fa : F A1 B1 C1)
          -> zimap (f1 compose f2) (g2 compose g1) (h2 compose h1) fa ≡ zimap f2 g2 h2 (zimap f1 g1 h1 fa)

zimap× : {A B C AA BB CC : Type 𝑢} ->
    (AA -> A) ->
    (B -> BB) ->
    (C -> CC)
    -> Function A (B × C) -> Function AA (BB × CC)
zimap× prepare fb fc a->bc aa = ×bimap fb fc ((a->bc compose prepare) aa)

ZifunctorFunctionProduct : Zifunctor {𝑢} \ A B C -> Function A (B × C)
ZifunctorFunctionProduct = record
  { zimap         = zimap×
  ; zimap-id      = {!   !}
  ; zimap-compose = {!   !}
  }

fun-dimap : forall {A B AA BB : Type 𝑢}
      -> (AA -> A)
      -> (B -> BB)
      -> (A -> B)
      -> (AA -> BB)
fun-dimap faa->a fb->bb fa->b = (fb->bb compose fa->b) compose faa->a

zimap+ : {A B C AA BB CC : Type 𝑢} ->
      (AA -> A) ->
      (B -> BB) ->
      (C -> CC) -> Function A (B + C) -> Function AA (BB + CC)
zimap+ prep fb fc a->bc = (bimap+ fb fc) compose (a->bc compose prep)

ZifunctorFunctionEither : Zifunctor {𝑢} \ A B C -> Function A (B + C)
ZifunctorFunctionEither = record
  { zimap         = zimap+
  ; zimap-id      = {!   !}
  ; zimap-compose = {!   !}
  }
