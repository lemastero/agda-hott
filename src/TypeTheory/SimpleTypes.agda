{-# OPTIONS --without-K --exact-split --safe #-}

module TypeTheory.SimpleTypes where

open import TypeTheory.Universes using (Type; 𝑢0; 𝑢; Universe)

-- empty type / void / nothing / initial object
data ZeroL {𝑢 : Universe} : Type 𝑢 where
                             -- no constructors
Zero : Type
Zero = ZeroL {𝑢0}

-- 0 elimination rule / 0 induction
-- forall P : 0 -> Universe
-- Π x : P , P x
0-elim : (P : Zero -> Type 𝑢)
                          -- no base case
                          -- no inductive case
 -> (z : Zero) -> P z     -- property P holds for all elements of type Zero
0-elim P ()

-- non dependent 0 elim
0-recursion : (Q : Type 𝑢)
  -> (z : Zero) -> Q
0-recursion Q z = 0-elim (\ x -> Q) z

is-empty : Type 𝑢 -> Type 𝑢
is-empty X = X -> Zero -- type is empty == there is function to the empty type

0-is-empty : is-empty Zero
0-is-empty = \ x -> x

absurd : (A : Type 𝑢) -> Zero -> A
absurd = 0-recursion

-- unit type / terminal object
{-
data One : Type 𝑢0 where
  <> : One
-}
data OneL {𝑢 : Universe} : Type 𝑢 where
  <> : OneL

One : Type
One = OneL {𝑢0}

-- for any property P of type One, if P(<>) it holds for <>
-- then P(x) it holds for all x: One
1-elim : (P : One -> Type 𝑢)
  -> P <>               -- base case
                        -- no inductive case
  -> (x : One) -> P x   -- property P holds for every element of One
1-elim P a <> = a

-- logic: P => (true -> P)
-- const[P](P)   : Unit => P
1-recursion : (P : Type 𝑢) ->
  P ->
  (One -> P)
1-recursion P a x = 1-elim (\ _ -> P) a x

-- unique function from any type to One
-- logic: A => true
unit : {A : Type 𝑢} -> A -> OneL {𝑢}
unit x = <>

-- 2 elements type / booleans
{-
data Bool : Type 𝑢0 where
  true : Bool
  false : Bool
-}

data BoolL {𝑢 : Universe} : Type 𝑢 where
  true : BoolL
  false : BoolL

Bool : Type
Bool = BoolL {𝑢0}

{-# BUILTIN BOOL Bool #-}
{-# BUILTIN FALSE false #-}
{-# BUILTIN TRUE true #-}

-- induction principle on Bool
Bool-elim : (P : Bool -> Type 𝑢)
 -> P true             -- base case true
 -> P false            -- base case false
 -> (b : Bool) -> P b  -- property P holds for all elements b
Bool-elim P aT aF true  = aT
Bool-elim P aT aF false = aF

-- is Bool-elim with args re-arranged
depenedent-on_if_then_else_ : (P : Bool -> Type 𝑢)
    -> (b : Bool)
    -> P true
    -> P false
    -> P b
depenedent-on P if true  then true-expr else false-expr = true-expr
depenedent-on P if false then true-expr else false-expr = false-expr

Bool-recursion : (P : Type 𝑢)
 -> P
 -> (Bool -> P -> P)
 -> Bool -> P
Bool-recursion P p fbp b = fbp b p

_&&_ : Bool -> Bool -> Bool
true && b = b
false && b = false

_||_ : Bool -> Bool -> Bool
true || b = true
false || b = b

_xor_ : Bool -> Bool -> Bool
true xor true = false
true xor false = true
false xor true = true
false xor false = false

--type of natural numbers
data Nat : Type 𝑢0 where
  zero : Nat
  succ : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

--Induction principle == Nat elimination rule
Nat-induction : (P : Nat -> Type 𝑢)
 -> P 0                               -- base case
 -> ((n : Nat) -> P n -> P (succ n))  -- inductive case
 -> (n : Nat) -> P n                  -- property P holds for all element of N
--Nat-induction P P0 f 0 = P0
Nat-induction P p0 fnp 0 = p0
Nat-induction P p0 fnp (succ n) = fnp n (Nat-induction P p0 fnp n)

--Recurson principle
Nat-recursion : (P : Type 𝑢)
 -> P
 -> (Nat -> P -> P)
 -> Nat -> P
Nat-recursion P p0 fnp n = Nat-induction
  (\ m -> P) -- fake dependent type P that Nat-induction want
  p0 fnp n

Nat-iteration : (P : Type 𝑢)
 -> P
 -> (P -> P)
 -> Nat -> P
Nat-iteration P p0 f n = Nat-recursion P p0 (\ _n p -> f p) n

-- function properties

->-refl : {X : Type 𝑢} -> X -> X
->-refl x = x

->-assoc : {X Y Z : Type 𝑢}
       -> (X -> Y) -> (Y -> Z) -> (X -> Z)
->-assoc f g x = g (f x)

id : {A : Type 𝑢} -> (A -> A)
id = ->-refl

id' : (A : Type 𝑢) -> (A -> A)
id' A = ->-refl

_compose_ : {X Y Z : Type 𝑢}
    -> (Y -> Z) -> (X -> Y)
    -> (X -> Z)
(g compose f) = ->-assoc f g

_andThen_ : {A B C : Type 𝑢}
    -> (A -> B) -> (B -> C)
    -> (A -> C)
_andThen_ = ->-assoc

const : {T U : Type 𝑢} -> T -> U -> T
const x _ = x
