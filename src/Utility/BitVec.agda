module Utility.BitVec where

open import ThesisPrelude
open import Algebra.Function
open import Utility.VecFuns
open import Utility.VecProps
open import Utility.ListLemmas
open import Utility.Elem
open import Utility.Bool

BitVec : Nat → Set
BitVec = Vec Bool

∷-vec-Inj : ∀{l} {n : Nat} {A : Set l} (x : A)
        → Injective (Vec._∷_ {A = A} {n = n} x)
∷-vec-Inj x xs .xs refl = refl

bitvec-xor : ∀{n} → BitVec n → BitVec n → BitVec n
bitvec-xor = vzip xor

bitvec-xor-self-inverse : ∀{n} → (xs ys : BitVec n)
                        → ys ≡ bitvec-xor xs (bitvec-xor xs ys) 
bitvec-xor-self-inverse [] [] = refl
bitvec-xor-self-inverse (x ∷ xs) (y ∷ ys) = cong₂ _∷_ (xor-self-inverse x y) (bitvec-xor-self-inverse xs ys)

bitvec-xor-Bij : ∀{n} → (xs : BitVec n)
               → Bijective (bitvec-xor xs)
bitvec-xor-Bij xs = bitvec-xor xs , bitvec-xor-self-inverse xs , bitvec-xor-self-inverse xs

all-bitvecs : ∀ n → List (BitVec n)
all-bitvecs zero = [ [] ]
all-bitvecs (suc n) = map (_∷_ false) (all-bitvecs n) ++ map (_∷_ true) (all-bitvecs n)

all-bitvecs-complete : ∀{n} → (v : BitVec n) → v ∈ all-bitvecs n
all-bitvecs-complete [] = here [] []
all-bitvecs-complete {suc n} (false ∷ v) =
  in-++-left (false ∷ v)
    (map (_∷_ false) (all-bitvecs n))
    (map (_∷_ true) (all-bitvecs n))
    (map-preserves-in (_∷_ false) v (all-bitvecs n) (all-bitvecs-complete v))
all-bitvecs-complete {suc n} (true ∷ v) =
  in-++-right (true ∷ v)
    (map (_∷_ false) (all-bitvecs n))
    (map (_∷_ true) (all-bitvecs n))
    (map-preserves-in (_∷_ true) v (all-bitvecs n) (all-bitvecs-complete v))

map-true-lem : ∀{n} (v : BitVec n) (xs : List (BitVec n))
             → ¬ (true ∷ v ∈ map {A = BitVec n} {B = BitVec (suc n)} (λ x → _∷_ false x) xs)
map-true-lem v [] () 
map-true-lem v (x ∷ xs) (there ._ ._ ._ p) = map-true-lem v xs p

map-false-lem : ∀{n} (v : BitVec n) (xs : List (BitVec n))
              → ¬ (false ∷ v ∈ map {B = BitVec (suc n)} (λ x → _∷_ true x) xs)
map-false-lem v [] () 
map-false-lem v (x ∷ xs) (there ._ ._ ._ p) = map-false-lem v xs p

all-bitvecs-unique : ∀{n} → (v : BitVec n) → (p : v ∈ all-bitvecs n) → p ≡ all-bitvecs-complete v
all-bitvecs-unique {zero} [] (here .[] .[]) = refl
all-bitvecs-unique {zero} [] (there .[] .[] .[] ())
all-bitvecs-unique {suc n} (true ∷ v) p
  with in-some-++ (true ∷ v) (map (_∷_ false) (all-bitvecs n)) (map (_∷_ true) (all-bitvecs n)) p
     | graphAt (in-some-++ (true ∷ v) (map (_∷_ false) (all-bitvecs n)) (map (_∷_ true) (all-bitvecs n))) p
all-bitvecs-unique {suc n} (true ∷ v) p | left pl | _ = ⊥-elim (map-true-lem v (all-bitvecs n) pl)
all-bitvecs-unique {suc n} (true ∷ v) p | right pr | ingraph pre
  rewrite sym (all-bitvecs-unique v (drop-map-lem (_∷_ true) (∷-vec-Inj true) v (all-bitvecs n) pr))
        | sym (map-preserves-Sec (_∷_ true) (∷-vec-Inj true) v (all-bitvecs n) pr)
        = in-some-++-Inj (true ∷ v)
                         (map (_∷_ false) (all-bitvecs n))
                         (map (_∷_ true) (all-bitvecs n))
                         p
                         (in-++-right (true ∷ v) (map (_∷_ false) (all-bitvecs n)) (map (_∷_ true) (all-bitvecs n)) pr)
                         (pre
                            ⟨≡⟩
                          in-some-++-right (true ∷ v)
                                           (map (_∷_ false) (all-bitvecs n))
                                           (map (_∷_ true) (all-bitvecs n))
                                           pr)
all-bitvecs-unique {suc n} (false ∷ v) p
  with in-some-++ (false ∷ v) (map (_∷_ false) (all-bitvecs n)) (map (_∷_ true) (all-bitvecs n)) p
     | graphAt (in-some-++ (false ∷ v) (map (_∷_ false) (all-bitvecs n)) (map (_∷_ true) (all-bitvecs n))) p
all-bitvecs-unique {suc n} (false ∷ v) p | left pl | ingraph ple
  rewrite sym (all-bitvecs-unique v (drop-map-lem (_∷_ false) (∷-vec-Inj false) v (all-bitvecs n) pl))
        | sym (map-preserves-Sec (_∷_ false) (∷-vec-Inj false) v (all-bitvecs n) pl)
        = in-some-++-Inj (false ∷ v)
                         (map (_∷_ false) (all-bitvecs n))
                         (map (_∷_ true) (all-bitvecs n))
                         p
                         (in-++-left (false ∷ v) (map (_∷_ false) (all-bitvecs n)) (map (_∷_ true) (all-bitvecs n)) pl)
                         (ple
                            ⟨≡⟩
                          in-some-++-left (false ∷ v)
                                          (map (_∷_ false) (all-bitvecs n))
                                          (map (_∷_ true) (all-bitvecs n))
                                          pl)
all-bitvecs-unique {suc n} (false ∷ v) p | right pr | _ = ⊥-elim (map-false-lem v (all-bitvecs n) pr)

mutual
  bitvec-filter-ff-helper : ∀{n} (xs : BitVec n)
                          → [ false ∷ xs ] ≡ filter (isYes ∘ (_==_ (false ∷ xs))) (map (_∷_ false) (all-bitvecs n))
  bitvec-filter-ff-helper {n} xs =
    [ false ∷ xs ]
      ≡⟨ {!!} ⟩
    filter (isYes ∘ (_==_ (false ∷ xs))) (map (_∷_ false) (all-bitvecs n))
    ∎
  
  bitvec-filter : ∀{n} (xs : BitVec n)
                → [ xs ] ≡ filter (isYes ∘ (_==_ xs)) (all-bitvecs n)
  bitvec-filter [] = refl
  bitvec-filter {(suc n)} (false ∷ xs) =
    [ false ∷ xs ]
      ≡⟨ list-++-right-identity [ false ∷ xs ] ⟩
    [ false ∷ xs ] ++ []
      ≡⟨ cong₂ _++_ {!!} {!!} ⟩
    filter (isYes ∘ (_==_ (false ∷ xs))) (map (_∷_ false) (all-bitvecs n)) ++ filter (isYes ∘ (_==_ (false ∷ xs))) (map (_∷_ true) (all-bitvecs n))
      ≡⟨ filter-append-dist (isYes ∘ (_==_ (false ∷ xs))) (map (_∷_ false) (all-bitvecs n)) (map (_∷_ true) (all-bitvecs n)) ⟩ʳ
    filter (isYes ∘ (_==_ (false ∷ xs))) (all-bitvecs (suc n))
    ∎
  bitvec-filter {n} (true ∷ xs) = {!!}
