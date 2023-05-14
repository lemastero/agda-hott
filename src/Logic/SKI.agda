{-# OPTIONS --without-K --exact-split --safe #-}

module Logic.SKI where

open import TypeTheory.Universes
open import TypeTheory.SimpleTypes

{- SKI combinators -}

combinatorK : {A E : Type 𝑢}
         -> A -> E
         -> A
combinatorK z _ = z

combinatorS : {S T E : Type 𝑢}
           -> (E -> (S -> T))
           -> (E -> S)
           -> E
           -> T
combinatorS est es e = est e (es e)

combinatorI : {A : Type 𝑢} -> (A -> A)
combinatorI = id
{--
combinatorI : {X : Type 𝑢} -> X -> X
combinatorI = combinatorS combinatorK ( λ x → _ )
--}
