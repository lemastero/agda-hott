{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module TypeTheory.Dependent-Types where

open import TypeTheory.Universes

{-
type theory: dependent sum type (Sigma)
logic: designated existance (we know which element fulfills condition)
programming: dependen product
homotopy theory: total space
-}

-- definition using data does not satisfy η-rule  xy = (fst x, snd y)
record Σ {X : Type 𝑢} (Y : X -> Type 𝑤) : Type (𝑢 umax 𝑤) where
  constructor
    _,_
  field
    x : X
    y : Y x

infixr 50 _,_

fst : {X : Type 𝑢} {Y : X -> Type 𝑤} -> Σ Y -> X
fst (x , y) = x

--    {X : Type 𝑢} {Y : X -> Type 𝑤} -> (xy : Σ Y) -> Y (fst xy)
snd : {X : Type 𝑢} {Y : X -> Type 𝑤} -> ((x , y) : Σ Y) -> Y x
snd (x , y) = y

Sigma : (X : Type 𝑢) (Y : X -> Type 𝑤) -> Type (𝑢 umax 𝑤)
Sigma X Y = Σ Y

syntax Sigma X (\ x -> y) = Σ x :: X , y

infix -1 Sigma

-- for property A and all z : Σ y proove that A z is enough to prove we have A(x,y) for x:X and y:Y x
-- called also: uncurry, Σ-elimination
Σ-elim : {X : Type 𝑢} {Y : X -> Type 𝑤} {P : Σ Y -> Type 𝑧}
 -> ((x : X) (y : Y x) -> P (x , y))  -- f : (x, Yx) -> P (x Yx)
 -> ((x , y) : Σ Y)                   -- w : Σ x, Y x
 -> P (x , y)
Σ-elim f (x , y) = f x y

Σ-uncurry : {X : Type 𝑢} {Y : X -> Type 𝑤} {P : Σ Y -> Type 𝑧}
 -> ((x : X) -> (y : Y x) -> P (x , y)) -- f: x -> y -> P (x y)
 -> ((x , y) : Σ Y)                     -- (x, y)
 -> P (x , y)                           -- P (x y)
Σ-uncurry = Σ-elim

-- inverse of Σ-induction

Σ-curry : {X : Type 𝑢} {Y : X -> Type 𝑤} {A : Σ Y -> Type 𝑧}
 -> (((x , y) : Σ Y) -> A (x , y))
 -> ((x : X) (y : Y x) -> A (x , y))
Σ-curry f x y = f (x , y)

_×_ : Type 𝑢 -> Type 𝑤 -> Type (𝑢 umax 𝑤)
X × Y = Σ x :: X , Y

infixr 30 _×_

{-
type theory: dependent product type Pi(x: X),A(x)
logic: universal quantifier
programming: dependen function
homotopy theory: space of sections
-}

Pi : {X : Type 𝑢} (A : X -> Type 𝑤) -> Type (𝑢 umax 𝑤)
Pi {𝑢} {𝑤} {X} A = (x : X) -> A x

syntax Pi X (λ x -> y) = Π x :: X , y

-- dependent and non-dependent functions composition
_Π-compose1_ : {X : Type 𝑢} {Y : Type 𝑤}
  {Z : Y -> Type 𝑧}
  -> ((y : Y) -> Z y)
  -> (f : X -> Y)
  -> (x : X) -> Z (f x)
(g Π-compose1 f) x = g (f x)

_Π-andThen_ : {X : Type 𝑢} {Y : Type 𝑤} {Z : Y -> Type 𝑧}
  -> (f : X -> Y)
  -> ((y : Y) -> Z y)
  -> (x : X) -> Z (f x)
f Π-andThen g = g Π-compose1 f

-- dependent functions composition
_Π-compose2_ : {X : Type 𝑢} {Y : X -> Type 𝑤}
            {Z : (a : X)(b : Y a) -> Type 𝑧}
         -> ( g : ( (a : X)(b : (Y a)) -> Z a b ) )
         -> ( f : ( (a : X) -> Y a ) )
         -> ( (a : X) -> (Z a (f a)) )
g Π-compose2 f = \ a -> g a (f a)

flip : {X : Type 𝑢} {Y : Type 𝑤} {Z : X -> Y -> Type 𝑧}
    -> ((x : X) (y : Y) -> Z x y)
    ----------------------------
    -> ((y : Y) (x : X) -> Z x y)
flip f = \ y x -> f x y

flip3 : {A : Type 𝑢} {B : Type 𝑤} {C : Type 𝑧} {Z : A -> B -> C -> Type ℓ}
    -> ((a : A) (b : B) (c : C) -> Z a b c)
    ----------------------------
    -> ((c : C) (b : B) (a : A) -> Z a b c)
flip3 f = \ c b a -> f a b c

domain : {X : Type 𝑢} {Y : Type 𝑤} -> (X -> Y) -> Type 𝑢
domain {U} {V} {X} {Y} f = X

codomain : {X : Type 𝑢} {Y : Type 𝑤} -> (X -> Y) -> (Type 𝑤)
codomain {U} {V} {X} {Y} f = Y
