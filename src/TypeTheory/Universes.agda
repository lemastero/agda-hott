{-# OPTIONS --without-K --exact-split --safe #-}

module TypeTheory.Universes where

open import Agda.Primitive public
 renaming (  Level to Universe   -- rename Level to Universe to match HoTT
          ; lzero to 𝑢0
          ; lsuc to usuc         -- next universe
          ; _⊔_ to _umax_        -- max of two universes
          ; Set to Type)

-- declare variables for Universes
variable ℓ 𝑢 𝑤 𝑧 : Universe

𝑢1 = usuc 𝑢0
