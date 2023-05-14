{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module FP.zio-prelude.parametrized.Covariant where

open import TypeTheory.Universes using (Type; 𝑢; usuc; Universe)
open import TypeTheory.SimpleTypes using (OneL; <>; id; _compose_; Nat) renaming (unit to 1unit)
open import TypeTheory.FunctionsProperties using (compose-id; compose-compose)
open import HoTT.Identity-Types using (refl; _≡_)
open import FP.Maybe using (Maybe; map-Maybe; maybe-map-id; maybe-map-compose)
open import FP.List using (List; []; _cons_; map-List; map-id; map-compose)
open import FP.Vec using (Vec; vMap; vMap-id; vMap-compose)
open import FP.Types using (Id; Function)
open import TypeTheory.Product using (_×_; _,,_)

-- https://github.com/zio/zio-prelude/blob/series/2.x/core/shared/src/main/scala/zio/prelude/Covariant.scala
-- https://github.com/zio/zio-prelude/blob/series/2.x/laws/shared/src/main/scala/zio/prelude/laws/CovariantLaws.scala
record Covariant (F : Type 𝑢 -> Type 𝑢) : Type (usuc 𝑢) where
  field
    -- operations
    map : forall {A B : Type 𝑢}
        -> (A -> B)
        -> F A -> F B
    -- laws
    identityLaw : forall {A : Type 𝑢}
          -> (fa : F A)
          -> map id fa ≡ fa
    compositionLaw : forall {A B C : Type 𝑢}
          -> (f : (A -> B))
          -> (g : (B -> C))
          -> (fa : F A)
          -> map (g compose f) fa ≡ map g (map f fa)
  -- derived operations
  fproduct : forall {A B : Type 𝑢}
      -> (A -> B)
      -> F A -> F (A × B)
  fproduct f = map (\ a -> a ,, f a)
  fproductLeft : forall {A B : Type 𝑢}
      -> (A -> B)
      -> F A -> F (B × A)
  fproductLeft f = map (\ a -> f a ,, a)
  as : forall {A B : Type 𝑢}
    -> F A
    -> B
    -> F B
  as fa b = map (\ _ -> b) fa
  unit : forall {A : Type 𝑢}
      -> F A
      -> F OneL
  unit = map 1unit
  -- TODO Functor composition

CovariantId : Covariant {𝑢} Id
CovariantId = record
  { map            = id
  ; identityLaw    = refl
  ; compositionLaw = \ f g fa -> refl (g (f fa))
  }

CovariantMaybe : Covariant {𝑢} Maybe
CovariantMaybe = record
  { map            = map-Maybe
  ; identityLaw    = maybe-map-id
  ; compositionLaw = maybe-map-compose
  }

CovariantList : Covariant {𝑢} List
CovariantList = record
  { map            = map-List
  ; identityLaw    = map-id
  ; compositionLaw = map-compose
  }

CovariantVec : (n : Nat) -> Covariant {𝑢} (\ X -> Vec X n )
CovariantVec n = record
  { map            = vMap
  ; identityLaw    = vMap-id n
  ; compositionLaw = vMap-compose n
  }

CovariantFunction : {X : Type 𝑢} -> Covariant {𝑢} (Function X)
CovariantFunction {X} = record
  { map            = _compose_
  ; identityLaw    = compose-id
  ; compositionLaw = compose-compose
  }
