module Utility.BitVec where

open import ThesisPrelude
open import Utility.VecFuns
open import Utility.VecProps
open import Utility.Elem
open import Utility.Bool

BitVec : Nat → Set
BitVec = Vec Bool

bitvec-xor : ∀{n} → BitVec n → BitVec n → BitVec n
bitvec-xor = vzip xor

all-bitvecs : ∀ n → List (BitVec n)
all-bitvecs zero = [ [] ]
all-bitvecs (suc n) = map (_∷_ false) (all-bitvecs n) ++ map (_∷_ true) (all-bitvecs n)

all-bitvecs-complete : ∀{n} → (v : BitVec n) → v ∈ all-bitvecs n
all-bitvecs-complete [] = here [] []
all-bitvecs-complete {suc n} (false ∷ v) =
  in-++-left (false ∷ v)
    (map (_∷_ false) (all-bitvecs n))
    (map (_∷_ true) (all-bitvecs n))
    (map-preserves-in v (all-bitvecs n) (_∷_ false) (all-bitvecs-complete v))
all-bitvecs-complete {suc n} (true ∷ v) =
  in-++-right (true ∷ v)
    (map (_∷_ false) (all-bitvecs n))
    (map (_∷_ true) (all-bitvecs n))
    (map-preserves-in v (all-bitvecs n) (_∷_ true) (all-bitvecs-complete v))

{- Interesting idea, but how do we do this?
all-bitvecs-unique : ∀{n} → (v : BitVec n) → (p : v ∈ all-bitvecs n) → p ≡ all-bitvecs-complete v
all-bitvecs-unique [] (here .[] .[]) = refl
all-bitvecs-unique [] (there .[] .[] .[] ())
all-bitvecs-unique (false ∷ v) p with all-bitvecs-complete v
... | bvc = {!!}
all-bitvecs-unique (true ∷ v) p = {!!}
-}