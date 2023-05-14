{-# OPTIONS --without-K --exact-split --safe #-}

module TypeTheory.LogicalEquiv where

open import TypeTheory.Universes using (Type; 𝑢; 𝑤; _umax_)
open import TypeTheory.SimpleTypes using (id; _andThen_)
open import TypeTheory.Product using (_×_; _,,_; ×-diag; ×-comm)

_<=>_ : Type 𝑢 -> Type 𝑤 -> Type (𝑢 umax 𝑤)
X <=> Y = (X -> Y) × (Y -> X)

-- logical equivalence to function
-- is accessing first or second element of pair
<=>-fst : {X : Type 𝑢} {Y : Type 𝑤} -> X <=> Y -> (X -> Y)
<=>-fst (x->y ,, y->x) = x->y

<=>-snd : {X : Type 𝑢} {Y : Type 𝑤} -> (X <=> Y) -> (Y -> X)
<=>-snd (x->y ,, y->x) = y->x

-- properties

<=>-refl : {A : Type 𝑢}
       -> (A <=> A)
<=>-refl {A} = ×-diag id

<=>-comm : {A : Type 𝑢}{B : Type 𝑢}
        -> (A <=> B) -> (B <=> A)
<=>-comm = ×-comm

<=>-assoc : {A B C : Type 𝑢}
           -> (A <=> B) -> (B <=> C)
           -> (A <=> C)
<=>-assoc(ab ,, ba) (bc ,, cb) = (ab andThen bc) ,, (cb andThen ba)
