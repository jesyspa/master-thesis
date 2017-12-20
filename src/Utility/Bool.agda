module Utility.Bool where

open import ThesisPrelude
open import Algebra.Function

xor : Bool → Bool → Bool
xor x y = isNo (x == y)

xor-self-inverse : (x y : Bool) → y ≡ xor x (xor x y)
xor-self-inverse false false = refl
xor-self-inverse false true = refl
xor-self-inverse true false = refl
xor-self-inverse true true = refl

xor-Bij : (x : Bool) → Bijective (xor x)
xor-Bij x = xor x , xor-self-inverse x , xor-self-inverse x 
