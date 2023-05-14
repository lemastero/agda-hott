{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.zio-prelude.concrete.Associative where

open import TypeTheory.Universes using (Type)
open import TypeTheory.SimpleTypes using (_compose_; Nat)
open import HoTT.Identity-Types using (_≡_)
open import FP.List using (List; _concat_; concat-assocLR)
open import Arithmetic.Nat-Peano using(_*_; _+_; assocRL-+; assocRL-*)


-- Semigroup
-- https://github.com/zio/zio-prelude/blob/series/2.x/core/shared/src/main/scala/zio/prelude/Associative.scala
-- https://github.com/zio/zio-prelude/blob/series/2.x/laws/shared/src/main/scala/zio/prelude/laws/AssociativeLaws.scala
record Associative (X : Type) : Type where
  field
    -- operations
    _combine_     : X -> X -> X
    -- laws
    associativityLaw : forall (A B C : X)
                 -> (A combine (B combine C)) ≡ ((A combine B) combine C)
  -- TODO derived operations

Associative-Nat+0 : Associative Nat
Associative-Nat+0 = record
  { _combine_        = _+_
  ; associativityLaw = assocRL-+
  }

Associative-Nat*1 : Associative Nat
Associative-Nat*1 = record
  { _combine_        = _*_
  ; associativityLaw = assocRL-*
  }

-- TODO min max
-- TODO vector vconcat
-- TODO String

Associative-List-concat : (X : Type) -> Associative (List X)
Associative-List-concat X = record
  { _combine_        = _concat_
  ; associativityLaw = concat-assocLR
  }
