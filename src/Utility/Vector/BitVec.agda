module Utility.Vector.BitVec where

open import ThesisPrelude
open import Algebra.Function
open import Algebra.Equality
open import Algebra.ExactSize
open import Utility.Num
open import Utility.Product
open import Utility.Vector.Functions
open import Utility.Vector.Props
open import Utility.List
open import Utility.Bool
open import Utility.Writer

BitVec : Nat → Set
BitVec = Vec Bool

∷-vec-Inj : ∀{l} {n : Nat} {A : Set l} (x : A)
        → Injective (Vec._∷_ {A = A} {n = n} x)
∷-vec-Inj x refl = refl

bitvec-xor : ∀{n} → BitVec n → BitVec n → BitVec n
bitvec-xor = vzip xor

bitvec-xorʳ : ∀{n} → BitVec n → BitVec n → BitVec n
bitvec-xorʳ = flip bitvec-xor

bitvec-xor-self-inverse : ∀{n} → (xs ys : BitVec n)
                        → ys ≡ bitvec-xor xs (bitvec-xor xs ys) 
bitvec-xor-self-inverse [] [] = refl
bitvec-xor-self-inverse (x ∷ xs) (y ∷ ys) = cong₂ _∷_ (xor-self-inverse x y) (bitvec-xor-self-inverse xs ys)

bitvec-xor-Bij : ∀{n} → (xs : BitVec n)
               → Bijective (bitvec-xor xs)
bitvec-xor-Bij xs = bitvec-xor xs , bitvec-xor-self-inverse xs , bitvec-xor-self-inverse xs

bitvec-xorʳ-self-inverse : ∀{n} → (xs ys : BitVec n)
                         → ys ≡ bitvec-xorʳ xs (bitvec-xorʳ xs ys) 
bitvec-xorʳ-self-inverse [] [] = refl
bitvec-xorʳ-self-inverse (x ∷ xs) (y ∷ ys) = cong₂ _∷_ (xorʳ-self-inverse x y) (bitvec-xorʳ-self-inverse xs ys)

bitvec-xorʳ-Bij : ∀{n} → (xs : BitVec n)
                → Bijective (bitvec-xorʳ xs) 
bitvec-xorʳ-Bij xs = bitvec-xorʳ xs , bitvec-xorʳ-self-inverse xs , bitvec-xorʳ-self-inverse xs

all-bitvecs : ∀ n → List (BitVec n)
all-bitvecs zero = [ [] ]
all-bitvecs (suc n) = map (_∷_ false) (all-bitvecs n) ++ map (_∷_ true) (all-bitvecs n)

all-bitvecs-length : ∀ n → pow2 n ≡ length (all-bitvecs n)
all-bitvecs-length zero = refl
all-bitvecs-length (suc n)
  rewrite length-append-dist (map (Vec._∷_ false) (all-bitvecs n)) (map (Vec._∷_ true) (all-bitvecs n))
        | sym (map-length (Vec._∷_ false) (all-bitvecs n))
        | sym (map-length (Vec._∷_ true) (all-bitvecs n))
        | sym (all-bitvecs-length n)
        = refl

all-bitvecs-complete : ∀{n} → (v : BitVec n) → v ∈ all-bitvecs n
all-bitvecs-complete [] = here [] []
all-bitvecs-complete {suc n} (false ∷ v) =
  in-++-left
    (map (_∷_ false) (all-bitvecs n))
    (map (_∷_ true) (all-bitvecs n))
    (map-preserves-in (_∷_ false) v (all-bitvecs n) (all-bitvecs-complete v))
all-bitvecs-complete {suc n} (true ∷ v) =
  in-++-right
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
  with in-some-++ (map (_∷_ false) (all-bitvecs n)) (map (_∷_ true) (all-bitvecs n)) p
     | graphAt (in-some-++ (map (_∷_ false) (all-bitvecs n)) (map (_∷_ true) (all-bitvecs n))) p
all-bitvecs-unique {suc n} (true ∷ v) p | left pl | _ = ⊥-elim (map-true-lem v (all-bitvecs n) pl)
all-bitvecs-unique {suc n} (true ∷ v) p | right pr | ingraph pre
  rewrite sym (all-bitvecs-unique v (drop-map-lem (_∷_ true) (∷-vec-Inj true) v (all-bitvecs n) pr))
        | sym (map-preserves-Sec (_∷_ true) (∷-vec-Inj true) v (all-bitvecs n) pr)
        = in-some-++-Inj (map (_∷_ false) (all-bitvecs n))
                         (map (_∷_ true) (all-bitvecs n))
                         (pre
                            ⟨≡⟩
                          in-some-++-right (true ∷ v)
                                           (map (_∷_ false) (all-bitvecs n))
                                           (map (_∷_ true) (all-bitvecs n))
                                           pr)
all-bitvecs-unique {suc n} (false ∷ v) p
  with in-some-++ (map (_∷_ false) (all-bitvecs n)) (map (_∷_ true) (all-bitvecs n)) p
     | graphAt (in-some-++ (map (_∷_ false) (all-bitvecs n)) (map (_∷_ true) (all-bitvecs n))) p
all-bitvecs-unique {suc n} (false ∷ v) p | left pl | ingraph ple
  rewrite sym (all-bitvecs-unique v (drop-map-lem (_∷_ false) (∷-vec-Inj false) v (all-bitvecs n) pl))
        | sym (map-preserves-Sec (_∷_ false) (∷-vec-Inj false) v (all-bitvecs n) pl)
        = in-some-++-Inj (map (_∷_ false) (all-bitvecs n))
                         (map (_∷_ true) (all-bitvecs n))
                         (ple
                            ⟨≡⟩
                          in-some-++-left (false ∷ v)
                                          (map (_∷_ false) (all-bitvecs n))
                                          (map (_∷_ true) (all-bitvecs n))
                                          pl)
all-bitvecs-unique {suc n} (false ∷ v) p | right pr | _ = ⊥-elim (map-false-lem v (all-bitvecs n) pr)

module _ {B : Set} where
  all-bitvecs-indexing-fun : ∀{n} (v : BitVec n) (b : B) → Index v [ v , b ] → Index v (annotate b (all-bitvecs n))
  all-bitvecs-indexing-fun {n} v b _ = ∈-to-annotate-Index v (all-bitvecs n) b (all-bitvecs-complete v)
  
  all-bitvecs-indexing-inv : ∀{n} (v : BitVec n) (b : B) → Index v (annotate b (all-bitvecs n)) → Index v [ v , b ]
  all-bitvecs-indexing-inv {n} v b _ = here v b []
  
  all-bitvecs-indexing-Ret : ∀{n} (v : BitVec n) (b : B)
                           → Retraction all-bitvecs-indexing-inv v b of all-bitvecs-indexing-fun v b
  all-bitvecs-indexing-Ret v b (here .v .b .[]) = refl
  all-bitvecs-indexing-Ret v b (there .v .(v , b) .[] ())
  
  all-bitvecs-indexing-Sec : ∀{n} (v : BitVec n) (b : B)
                           → Section all-bitvecs-indexing-inv v b of all-bitvecs-indexing-fun v b
  all-bitvecs-indexing-Sec {n} v b p = Index-to-∈-Inj v (annotate b (all-bitvecs n)) pk 
    where p-ret : all-bitvecs n ≡ map fst (annotate b (all-bitvecs n))
          p-ret = map-lift-ret fst (rev-pair b) (λ a → refl) (all-bitvecs n)
          pk : Index-to-∈ v (annotate b (all-bitvecs n)) p ≡
               Index-to-∈ v (annotate b (all-bitvecs n)) (∈-to-annotate-Index v (all-bitvecs n) b (all-bitvecs-complete v))
          pk =
            Index-to-∈ v (annotate b (all-bitvecs n)) p
              ≡⟨ flip-transport (_∈_ v)
                                p-ret
                                (all-bitvecs-complete v)
                                (Index-to-∈ v (annotate b (all-bitvecs n)) p)
                                (sym (all-bitvecs-unique v (transport (_∈_ v) (sym p-ret) (Index-to-∈ v (annotate b (all-bitvecs n)) p))) ) ⟩ʳ
            transport (_∈_ v) p-ret (all-bitvecs-complete v)
              ≡⟨ Index-to-∈-Ret v (map (rev-pair b) (all-bitvecs n))
                                  (transport (_∈_ v) p-ret (all-bitvecs-complete v)) ⟩
            Index-to-∈ v (annotate b (all-bitvecs n))
                         (∈-to-Index v (annotate b (all-bitvecs n))
                         (transport (_∈_ v) p-ret (all-bitvecs-complete v)))
              ≡⟨ refl ⟩
            Index-to-∈ v (annotate b (all-bitvecs n)) (∈-to-annotate-Index v (all-bitvecs n) b (all-bitvecs-complete v))
            ∎
  
  all-bitvecs-indexing : ∀{n} (v : BitVec n) (b : B) → Index v [ v , b ] ↔ Index v (annotate b (all-bitvecs n))
  all-bitvecs-indexing v b = all-bitvecs-indexing-fun v b , all-bitvecs-indexing-inv v b , all-bitvecs-indexing-Ret v b , all-bitvecs-indexing-Sec v b

  all-bitvecs-size : ∀{n} (v : BitVec n) → HasSize (v ∈ all-bitvecs n) 1
  all-bitvecs-size {n} v = size1-lem (v ∈ all-bitvecs n) (all-bitvecs-complete v) (all-bitvecs-unique v)
  
  filter-bitvecs-lem : ∀{n} (v : BitVec n) → [ v ] ≡ filter (isYes ∘ (_==_ v)) (all-bitvecs n)
  filter-bitvecs-lem {n} v = singleton-elem v (all-bitvecs n) (all-bitvecs-size v)


  all-bitvecs-filter-vals : ∀{n} (v : BitVec n) (b : B)
                          → [ b ] ≡ filter-vals v (annotate b (all-bitvecs n))
  all-bitvecs-filter-vals {n} v b =
    [ b ]
      ≡⟨ refl ⟩
    map (const b) [ v ]
      ≡⟨ map-snd-annotate-const b ([ v ]) ⟩
    map snd (annotate b [ v ]) 
      ≡⟨ cong (λ e → map snd (annotate b e)) (filter-bitvecs-lem v) ⟩
    map snd (annotate b (filter (isYes ∘ (_==_ v)) (all-bitvecs n)))
      ≡⟨ cong (map snd) (comm-annotate v b (all-bitvecs n)) ⟩
    filter-vals v (annotate b (all-bitvecs n))
    ∎


