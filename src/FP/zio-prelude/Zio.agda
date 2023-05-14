{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.zio-prelude.ZIO where

open import TypeTheory.Universes using (Type; 𝑢)
open import TypeTheory.SimpleTypes using (id; _compose_)
open import HoTT.Identity-Types using (_≡_; refl)
open import TypeTheory.Sum using (_+_; bimap+)

record ZIO (R E A : Type 𝑢) : Type 𝑢 where
  field
    run : R -> (E + A)
  -- derived functions
  mapOut : {B : Type 𝑢}
     -> (A -> B)
     -> ZIO R E B
  mapOut f = record { run = (bimap+ id f) compose run }
  mapErr : {EE : Type 𝑢}
     -> (E -> EE)
     -> ZIO R EE A
  mapErr f = record { run = (bimap+ f id) compose run }
  prepare : {RR : Type 𝑢}
     -> (RR -> R)
     -> ZIO RR E A
  prepare f = record { run = run compose f }

  {-
  flatMap : (B : Type 𝑢)
         -> (A -> ZIO R E B)
         -> ZIO R E B
  flatMap B f = record { run = \ r -> {! (run r)  !} }
  -}
