{-# OPTIONS --without-K --exact-split --safe --no-unicode #-}

module HoTT.Identity-Types where

open import TypeTheory.Universes
open import TypeTheory.SimpleTypes
open import TypeTheory.Dependent-Types

-- identity type (identification, equality)

data _≡_ {X : Type 𝑢} : X -> X -> Type 𝑢 where
  refl : (x : X) -> x ≡ x

infix   0 _≡_

{-# BUILTIN EQUALITY _≡_ #-}

Path : (A : Type 𝑢) -> A -> A -> Type 𝑢
Path A x y = x ≡ y

syntax Path A x y = x ≡ y [ A ]

-- to proove property of Id it is enough to prove the easy case - refl
-- adding univalence and HITs makes Id have many elements
-- ≡-elim
J : (X : Type 𝑢)
    ( A : ((x y : X)  -> x ≡ y -> Type 𝑤) ) -- A is property of Id
 -> ((x : X) -> A x x (refl x))                 -- show that property holds for refl                                        -- no iductive case
 -> (x y : X) (p : x ≡ y) -> A x y p            -- then it holds for evry member of Id x y
J X A f x x (refl x) = f x

-- properties

≡-refl : {X : Type 𝑢} (x : X)
      -> x ≡ x
≡-refl x = refl x

≡-comm : {X : Type 𝑢} {x y : X}
      -> x ≡ y -> y ≡ x
≡-comm (refl x) = refl x

≡-transitive : {X : Type 𝑢} {x y z : X}
       -> (x ≡ y) -> (y ≡ z) -> (x ≡ z)
≡-transitive p (refl y) = p

-- congruence relation
≡-cong : {X : Type 𝑢} {Y : Type 𝑤}
      (f : X -> Y) {x y : X}
   -> (x ≡ y)
   -> f x ≡ f y
≡-cong f (refl x) = refl (f x)

-- Leibnitz principle: equal things satisfy the same properties
-- transport along ≡
-- substitute x with y in expression P depending on x
transport : {X : Type 𝑢}
   (P : X -> Type 𝑤)            -- P is property
   {x x' : X}                   -- forall x,y
   -> x ≡ x'                    -- if they are equal
   -> P x                       -- P holds for x
   -> P x'                      -- then P holds for y
transport P (refl x) px = px

≡->Fun : {X Y : Type 𝑢} -> X ≡ Y -> X -> Y
≡->Fun {U} = transport id

! : {X : Type 𝑢} {x y : X} -> x ≡ y -> y ≡ x
! = ≡-comm

-- composition of identity types
_∙_ : {X : Type 𝑢} {x y z : X} -> x ≡ y -> y ≡ z -> x ≡ z
_∙_ = ≡-transitive

infix 7 _∙_

-- groupoid laws
∙assoc : {A : Type} {x y z w : A}
         (p : x ≡ y)
         (q : y ≡ z)
         (r : z ≡ w)
         -> (p ∙ (q ∙ r)) ≡ ((p ∙ q) ∙ r) [ x ≡ w [ A ] ]
∙assoc p q (refl x) = refl (p ∙ q)

∙unit-left : {A : Type} {x y z w : A}
       -> (p : x ≡ y)
       -> (refl _ ∙ p) ≡ p
∙unit-left (refl x) = refl (refl x)

∙unit-right : {A : Type} {x y z w : A}
       -> (p : x ≡ y)
       -> (p ∙ refl _) ≡ p
∙unit-right p = refl p

!-inverse-left : {A : Type} {x y : A}
                  -> (p : x ≡ y)
                  -> (! p ∙ p) ≡ refl _
!-inverse-left (refl x) = refl (refl x)

!-inverse-right : {A : Type} {x y : A}
                   -> (p : x ≡ y)
                   -> (p ∙ ! p) ≡ refl _
!-inverse-right (refl x) = refl (refl x)


-- access elements of ≡
≡fst : { X : Type 𝑢} {x y : X} -> x ≡ y -> X
≡fst {U} {X} {x} {y} p = x

≡snd : { X : Type 𝑢} {x y : X} -> x ≡ y -> X
≡snd {U} {X} {x} {y} p = y

-- alternative names

-- apply function under =
ap : {X : Type 𝑢} {Y : Type 𝑤} (f : X -> Y) {x y : X}
  -> (x ≡ y) -> f x ≡ f y
ap = ≡-cong

ap2 : {X : Type 𝑢} {Y : Type 𝑤} {Z : Type 𝑧}
      (f : X -> Y -> Z) {x x' : X} {y y' : Y}
  -> (x ≡ x') -> (y ≡ y') -> f x y ≡ f x' y'
ap2 f (refl x) (refl y) = refl (f x y)

cong : {X Y : Set} (f : X -> Y) {x y : X} -> (x ≡ y) -> f x ≡ f y
cong = ≡-cong

≡-swap : {X : Type 𝑢} {x y : X} -> x ≡ y -> y ≡ x
≡-swap = ≡-comm

≡-sym : {X : Type 𝑢} {x y : X} -> x ≡ y -> y ≡ x
≡-sym = ≡-comm

≡-inv : {X : Type 𝑢} {x y : X} -> x ≡ y -> y ≡ x
≡-inv = ≡-comm

-- Utilities for writing proofs

_=$=_ : {X Y : Type 𝑢}{f g : X -> Y}{x1 x2 : X} ->
         f ≡ g -> x1 ≡ x2 -> f x1 ≡ g x2
refl f =$= (refl x) = refl (f x)

[Proof]_ : {X : Type 𝑢}{x y : X} -> (x ≡ y) -> (x ≡ y)
[Proof]_ x=y = x=y

_=[]_ : {X : Type 𝑢}(x {y} : X) -> (x ≡ y) -> (x ≡ y)
x =[] x=y = x=y

_=[_>=_ : {X : Type 𝑢}(x : X){y z : X} -> (x ≡ y) -> (y ≡ z) -> (x ≡ z)
x =[ x=y >= x=z = ≡-transitive x=y x=z

-- Yoneda embedding C(B,A) iso forall x: c(a,x)-> c(b,x)
-- for equality idirect equality a == b <=> forall c: (a <= c) -> (b <= c)
_=<_]=_ : {X : Type 𝑢}(x : X){y z : X} -> (y ≡ x) -> (y ≡ z) -> (x ≡ z)
x =< refl x ]= x==z = x==z

infix 1 [Proof]_
infixr 2 _=[_>=_ _=<_]=_ _=[]_
infix 3 _[QED]

_≡⟨_⟩_ : {X : Type 𝑢}(x : X){y z : X} -> (x ≡ y) -> (y ≡ z) -> (x ≡ z)
x ≡⟨ x=y ⟩ y=z = ≡-transitive x=y y=z

-- ≡ reflexivity
_[QED] : {X : Type 𝑢}(x : X) -> x ≡ x
_[QED] = ≡-refl

infixr 2 _≡⟨_⟩_

-- involution

is-involution : {X : Type} -> (X -> X) -> Type
is-involution {X} f = (x : X) -> f (f x) ≡ x

-- identity for function

->left-identity : {S T : Type} (f : S -> T) -> (id andThen f) ≡ f
->left-identity = refl

->right-identity : {S T : Type} (f : S -> T) -> (f andThen id) ≡ f
->right-identity = refl

->assocRL : {Q R S T : Type}
      (f : Q -> R)
      (g : R -> S)
      (h : S -> T) ->
      ------------------------
      ((f andThen g) andThen h) ≡ (f andThen (g andThen h))
->assocRL = \ f g h -> refl ( (f andThen g) andThen h )

->assocLR : {Q R S T : Type}
      (f : Q -> R)
      (g : R -> S)
      (h : S -> T) ->
      ------------------------
      (f andThen (g andThen h)) ≡ ((f andThen g) andThen h)
->assocLR f g h = ≡-comm (->assocRL f g h)
