{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

--https://github.com/pigworker/CS410-16/blob/master/lectures/CS410-Functor.agda

module FP.Abstractions.Monad where

open import TypeTheory.Universes using (Type; 𝑢; usuc; Universe)
open import TypeTheory.SimpleTypes using (OneL; <>; unit; id; _compose_)
open import HoTT.Identity-Types using (refl; _≡_)
open import FP.Maybe using (Maybe; Just; flatMap-Maybe;
  maybe-flatMap-just-f; maybe-flatMap-f-just; maybe-flatMap-compose)
open import FP.List using (List; []; _cons_; map-List ; map-id; map-compose; list; flatMap-List)
open import TypeTheory.Sum using (_+_)

record Monad (F : Type 𝑢 -> Type 𝑢) : Type (usuc 𝑢) where
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

MonadMaybe : Monad {𝑢} Maybe
MonadMaybe = record
  { return = Just
  ; _>>=_ = flatMap-Maybe
  ; return-flatmap = maybe-flatMap-just-f
  ; flatmap-return = maybe-flatMap-f-just
  ; flatmap-compose = maybe-flatMap-compose
  }

MonadList : Monad {𝑢} List
MonadList = record
  { return = list
  ; _>>=_ = \ xs f -> flatMap-List f xs
  ; return-flatmap = {!   !}
  ; flatmap-return = {!   !}
  ; flatmap-compose = {!   !}
  }

MonadEither : (E : Type 𝑢) -> Monad {𝑢} (\ A -> E + A)
MonadEither E = record
  { return = {!   !}
  ; _>>=_ = {!   !}
  ; return-flatmap = {!   !}
  ; flatmap-return = {!   !}
  ; flatmap-compose = {!   !}
  }
