{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.zio-prelude.concrete.Identity where

open import TypeTheory.Universes using (Type)
open import TypeTheory.SimpleTypes using (_compose_; Nat; zero; succ)
open import HoTT.Identity-Types using (refl; _≡_)
open import Arithmetic.Nat-Peano using
  ( _*_; *right-identity; *left-identity
  ; _+_; +right-identity; +left-identity)
open import FP.List using (List; _concat_; []; concat-nil; nil-concat)

-- Unital
-- https://github.com/zio/zio-prelude/blob/series/2.x/core/shared/src/main/scala/zio/prelude/Identity.scala
-- https://github.com/zio/zio-prelude/blob/series/2.x/laws/shared/src/main/scala/zio/prelude/laws/IdentityLaws.scala
record Identity (X : Type) : Type where
  field
    -- operations
    _combine_     : X -> X -> X
    identityLaw      : X
    leftIdentityLaw  : forall (A : X) -> (identity combine A) ≡ A
    rightIdentityLaw : forall (A : X) -> (A combine identity) ≡ A
  -- TODO derived operations

Identity-Nat+0 : Identity Nat
Identity-Nat+0 = record
  { _combine_     = _+_
  ; identityLaw      = zero
  ; leftIdentityLaw  = +left-identity
  ; rightIdentityLaw = +right-identity
  }

Identity-Nat*1 : Identity Nat
Identity-Nat*1 = record
  { _combine_     = _*_
  ; identityLaw      = succ zero
  ; leftIdentityLaw  = *left-identity
  ; rightIdentityLaw = *right-identity
  }

-- TODO min max
-- TODO vector vconcat
-- TODO String

Identity-List-concat : (X : Type) -> Identity (List X)
Identity-List-concat X = record
  { _combine_     = _concat_
  ; identityLaw      = []
  ; leftIdentityLaw  = nil-concat
  ; rightIdentityLaw = concat-nil
  }
