{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

--https://github.com/pigworker/CS410-16/blob/master/lectures/CS410-Functor.agda

module FP.Abstractions.Applicative where

open import TypeTheory.Universes using (Type; 𝑢; usuc)
open import TypeTheory.SimpleTypes using (OneL; <>; unit; id; _compose_)
open import HoTT.Identity-Types using (refl; _≡_)
open import FP.Types using (Id)

record Applicative (F : Type 𝑢 -> Type 𝑢) : Type (usuc 𝑢) where
  field
    -- operations
    pure : forall {A : Type 𝑢} -> A -> F A
    _<*>_ : forall {A B : Type 𝑢} -> F (A -> B) -> F A -> F B
    -- laws
    identity : forall {A : Type 𝑢}
               -> (fa : F A)
               -> ((pure id) <*> fa) ≡ fa
    composition : forall {A B C : Type 𝑢}
               -> (fbc : F (B -> C))
               -> (fab : F (A -> B))
               -> (fa : F A)
               -> pure (\ f g x -> f (g x)) <*> fbc <*> fab <*> fa ≡ fbc <*> (fab <*> fa)
    homomorphism : forall {A B : Type 𝑢}
               -> (f : A -> B)
               -> (x : A)
               -> pure (f x) ≡ pure f <*> pure x
    interchange : forall {A B : Type 𝑢} (fab : F (A -> B))(a : A)
               -> fab <*> pure a ≡ pure (\ f -> f a) <*> fab
  -- TODO derived operations
  infixl 10 _<*>_

ApplicativeId : Applicative {𝑢} Id
ApplicativeId = record
  { pure         = id
  ; _<*>_        = id
  ; identity     = refl
  ; composition  = \ fbc fab fa -> refl (fbc (fab fa))
  ; homomorphism = \ f x -> refl (f x)
  ; interchange  = \ fab a -> refl (fab a)
  }
