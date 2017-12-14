module Utility.Bool where

open import ThesisPrelude

xor : Bool → Bool → Bool
xor x y = isNo (x == y)
