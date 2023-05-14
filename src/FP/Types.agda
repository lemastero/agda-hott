{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.Types where

open import TypeTheory.Universes using (Type; 𝑢)

Id : Type 𝑢 -> Type 𝑢
Id A = A

Function : Type 𝑢 -> Type 𝑢 -> Type 𝑢
Function = \ A B -> ( x : A ) -> B
