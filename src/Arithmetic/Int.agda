{-# OPTIONS --without-K --exact-split --safe #-}

module Arithmetic.Int where

open import TypeTheory.Universes
open import TypeTheory.SimpleTypes
open import HoTT.Identity-Types

data Z : Type where
  in-neg : Nat -> Z
  in-pos : Nat -> Z
  z0 : Z

z-1 z1 : Z
z-1 = in-neg 0
z1 = in-pos 0

suc-Z : Z -> Z
suc-Z (in-pos (succ n)) = in-pos (succ (succ n))
suc-Z (in-pos 0)        = in-pos 1
suc-Z z0                = z1
suc-Z (in-neg 0)        = z0
suc-Z (in-neg (succ n)) = in-neg n

pred-Z : Z -> Z
pred-Z (in-neg n)        = in-neg (succ n) -- -n  => -(n+1)
pred-Z z0                = z-1              -- 0 => -1
pred-Z (in-pos 0)        = z0               -- 1   => 0
pred-Z (in-pos (succ n)) = in-pos n         -- n+1 => n

_+Z_ : Z -> (Z -> Z)
x +Z (in-pos (succ y)) = (suc-Z x) +Z (in-pos y)
x +Z (in-pos 0)        = suc-Z x
x +Z z0                = x
x +Z (in-neg 0)        = pred-Z x
x +Z (in-neg (succ y)) = (pred-Z x) +Z (in-neg y)

-Z : Z -> Z
-Z (in-neg x) = in-pos x
-Z (in-pos x) = in-neg x
-Z z0         = z0

_*Z_ : Z -> (Z -> Z)
x *Z (in-pos 0)        = x
x *Z (in-pos (succ y)) = x +Z (x *Z (in-pos y))
x *Z z0                = z0
-- you could handle both negative cases in one go by switching sign,
-- but Agda do not like it
x *Z (in-neg 0)        = -Z x
x *Z (in-neg (succ y)) = (-Z x) +Z ((-Z x) *Z (in-pos y))

-- +Zleft-identity (succ n) = cong succ (+left-identity n)
+Zright-identity : (z : Z)
                  --------------
               -> (z +Z z0) ≡ z
+Zright-identity z = refl z
