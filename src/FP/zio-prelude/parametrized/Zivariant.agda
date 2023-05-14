{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.zio-prelude.parametrized.Zivariant where

open import TypeTheory.Universes using (Type; 𝑢; usuc; Universe)
open import TypeTheory.SimpleTypes using (OneL; <>; unit; id; _compose_)
open import TypeTheory.Sum using (_+_; bimap+)
open import HoTT.Identity-Types using (refl; _≡_)
open import FP.Types using (Function)
open import TypeTheory.Product using (_×_; ×bimap; ×bimap-compose; ×bimap-id)
open import FP.zio-prelude.ZIO using (ZIO)

record Zivariant (F : Type 𝑢 -> Type 𝑢 -> Type 𝑢 -> Type 𝑢) : Type (usuc 𝑢) where
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

ZivariantFunctionEither : Zivariant {𝑢} ( \ In Err Out -> In -> (Err × Out))
ZivariantFunctionEither = record
  { zimap         = \ fin ferr fout fab x -> ×bimap ferr fout ((fab compose fin) x)
  ; zimap-id      = {!   !}
  ; zimap-compose = {!   !}
  }

ZivariantFunctionProduct : Zivariant {𝑢} ( \ A E C -> A -> (E + C))
ZivariantFunctionProduct = record
  { zimap         = \ fa fe fc faec aa -> bimap+ fe fc (faec (fa aa))
  ; zimap-id      = {!   !}
  ; zimap-compose = {!   !}
  }

ZivariantZIO : Zivariant {𝑢} ZIO
ZivariantZIO = record
  { zimap         = \ fa fb fc z -> mapErr (mapOut (prepare z fa) fc) fb
  ; zimap-id      = {!   !}
  ; zimap-compose = {!   !}
  } where open ZIO
