{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.zio-prelude.parametrized.AssociativeBoth where

open import TypeTheory.Universes using (Type; 𝑢; usuc; Universe)
open import TypeTheory.SimpleTypes using (OneL; <>; unit; id; _compose_; Nat)
open import TypeTheory.FunctionsProperties using (compose-id; compose-compose)
open import HoTT.Identity-Types using (refl; _≡_)
open import FP.Maybe using (Maybe; map-Maybe; maybe-map-id; maybe-map-compose)
open import FP.List using (List; []; _cons_; map; map-id; map-compose)
open import FP.Types using (Id)
open import Arithmetic.Nat-Peano using(_*_; _+_; assocRL-+; assocRL-*)
open import FP.List using (List; _concat_; []; _cons_;
  concat-nil; nil-concat; concat-assocLR)
open import TypeTheory.Product using (_×_; ×-comm; ×bimap)

-- Semigroup
-- https://github.com/zio/zio-prelude/blob/series/2.x/core/shared/src/main/scala/zio/prelude/AssociativeBoth.scala
-- https://github.com/zio/zio-prelude/blob/series/2.x/laws/shared/src/main/scala/zio/prelude/laws/AssociativeBothLaws.scala
record AssociativeBoth (F : Type -> Type) : Type where
  field
    -- operations
    _zip_     : forall (A B : Type) -> F A -> F B -> F (A × B)
    -- laws
    associativity : forall (A B C : Type)
                 -> (F A) zip ? ≡ ? --((F A zip F B) zip F C)
  -- TODO derived operations

{-
AssociativeBoth-Nat+0 : AssociativeBoth Nat
AssociativeBoth-Nat+0 = record
  { _combine_     = _+_
  ; associativity = assocRL-+
  }
-}
