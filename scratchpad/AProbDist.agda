{-# OPTIONS --allow-unsolved-metas #-}
module AProbDist where

open import MyPrelude
open import AbstractProb
open import ListLemmas
open import Monoid
open import MonoidInstances
open import MonoidLemmas
open import AbstractHelpers
open import Preorder

sumSnd : ∀{A n} → List (A × Fixed n) → XFixed 
sumSnd = sumF ∘ map snd

IsSubDist : ∀{A n} → List (A × Fixed n) → Set
IsSubDist = XIsProb ∘ sumSnd

sumSnd-simplify : ∀{A n} → (a : A) → (v : Fixed n) → (xs : List (A × Fixed n)) 
                → sumSnd ((a , v) ∷ xs) ≡ toXFixed v +XF sumSnd xs
sumSnd-simplify a v xs = refl

data SubDist (A : Set) : Set where
  subdist : (xs : List (A × Prob)) → IsSubDist xs → SubDist A

return-subdist-lem : ∀{A} → (a : A) → IsSubDist [ a , 1F ]
return-subdist-lem a rewrite sumSnd-simplify a 1F [] | sym (0XF-+XF-right-identity (zero , 1F)) = x-identity 1F

return : ∀{A} → A → SubDist A
return a = subdist [ a , 1F ] (return-subdist-lem a)

infix 2 _withEquiv_
_withEquiv_ : ∀{A B : Set}
       → A → A ≡ B
       → B
a withEquiv refl = a

-- TODO: Any better way to do this thing?
bind-helper-2 : {B : Set} → Prob → B × Prob → B × Prob 
bind-helper-2 p (b , q) = b , p *F q withEquiv sym (cong Fixed (mul-bs-zero-left-identity zero))

bind-helper : {A B : Set} → (A → SubDist B) → A × Prob → List (B × Prob)
bind-helper {A} {B} f (a , p) with f a
... | subdist xs _ = map (bind-helper-2 p) xs

bind-subdist-lem-2 : ∀{A B} → (f : A → SubDist B) → (xs : List (A × Prob))
                   → sumSnd (concatMap (bind-helper f) xs) ≤XF sumSnd xs
bind-subdist-lem-2 f xs =
  sumF (map snd (concatMap (bind-helper f) xs))
    ≤⟨ {!!} ⟩
  {!!}
    ≤⟨ {!!} ⟩
  sumF (map snd xs)
  [ Preorder-XF ]∎

bind-subdist-lem : ∀{A B} → (f : A → SubDist B) → (xs : List (A × Prob))
                 → IsSubDist xs
                 → IsSubDist (concatMap (bind-helper f) xs)
bind-subdist-lem f xs p = bounded-by-prob (bind-subdist-lem-2 f xs) p

_>>=_ : ∀{A B} → SubDist A → (A → SubDist B) → SubDist B
_>>=_ {A} {B} (subdist xs p) f = subdist (concatMap (bind-helper f) xs) (bind-subdist-lem f xs p)

{-
bh2-id-lem2 : {B : Set} → (bq : B × Prob) → bq ≡ bind-helper-2 1F bq
bh2-id-lem2 (b , q) = refl
    
Dist-right-id : ∀{A B} → {a : A} → {f : A → SubDist B} → f a ≡ return a >>= f
Dist-right-id {A} {B} {a} {f} =
  f a
    ≡⟨ map-weak-id-lem (bind-helper-2 1F) (f a) bh2-id-lem2 ⟩
  map (bind-helper-2 1F) (f a)
    ≡⟨ right-append-lem ⟩
  map (bind-helper-2 1F) (f a) ++ []
    ≡⟨ refl ⟩
  concat [ map (bind-helper-2 1F) (f a) ]
    ≡⟨ refl ⟩
  concatMap (bind-helper f) [ a , 1F ]
  ∎

totalProbability : ∀{A} → Dist A → Prob
totalProbability = mconcat {{MonoidProbPlus}} ∘ map snd

IsDist : ∀{A} → Dist A → Set
IsDist xs = 1F ≡ totalProbability xs

Dist-return : ∀{A} → (a : A) → IsDist (return a)
Dist-return a = refl

Dist-bind-helper-4 : (p : Prob) → (xs : List Prob)
                   → p *F mconcat xs ≡ mconcat (map (_*F_ p) xs)
Dist-bind-helper-4 p [] rewrite sym (mconcat-empty-lem {{MonoidProbPlus}}) = sym (0F-*F-left-nil p)
Dist-bind-helper-4 p (x ∷ xs) =
  p *F (x <> mconcat xs)
    ≡⟨ {!!} ⟩ -- oops, this can't be proven. bugger.
  p *F x <> (p *F mconcat xs)
    ≡⟨ cong (λ e → p *F x <> e) (Dist-bind-helper-4 p xs) ⟩
  p *F x <> mconcat (map (_*F_ p) xs)
  ∎

-- bind-helper-2 p (b , q) = b , p *F q
Dist-bind-helper-3 : ∀{B} → (p : Prob) → (x : B × Prob)
                   → (_*F_ p ∘ snd) x ≡ snd (bind-helper-2 p x)
Dist-bind-helper-3 p (b , q) = refl 

Dist-bind-helper-2 : ∀{A B} → (f : A → Dist B) → (a : A) → (p : Prob)
                   → IsDist (f a) 
                   → p ≡ mconcat (map snd (bind-helper f (a , p)))
Dist-bind-helper-2 f a p pf =
  p
    ≡⟨ 1F-*F-right-identity p ⟩
  p *F 1F
    ≡⟨ cong (_*F_ p) pf ⟩
  p *F mconcat (map snd (f a))
    ≡⟨ Dist-bind-helper-4 p (map snd (f a)) ⟩
  mconcat (map (_*F_ p) (map snd (f a)))
    ≡⟨ cong mconcat (sym (map-compose-lem (_*F_ p) snd (f a))) ⟩
  mconcat (map (_*F_ p ∘ snd) (f a))
    ≡⟨ cong mconcat (map-equiv-lem (_*F_ p ∘ snd) (snd ∘ bind-helper-2 p) (f a) (Dist-bind-helper-3 p)) ⟩
  mconcat (map (snd ∘ bind-helper-2 p) (f a))
    ≡⟨ cong mconcat (map-compose-lem snd (bind-helper-2 p) (f a)) ⟩
  mconcat (map snd (map (bind-helper-2 p) (f a)))
  ∎

Dist-bind : ∀{A B} → (da : Dist A) → (f : A → Dist B)
          → IsDist da
          → ((a' : A) → IsDist (f a'))
          → IsDist (da >>= f)
Dist-bind da f pda pf =
  1F
    ≡⟨ pda ⟩
  mconcat (map snd da)
    ≡⟨ {!!} ⟩
  mconcat (map mconcat {!!})
    ≡⟨ {!!} ⟩
  mconcat (map (mconcat ∘ map snd ∘ bind-helper f) da)
    ≡⟨ cong mconcat (map-compose-lem mconcat (map snd ∘ bind-helper f) da) ⟩
  mconcat (map mconcat (map (map snd ∘ bind-helper f) da))
    ≡⟨ sym (mconcat-concat-swap-lem (map (map snd ∘ bind-helper f) da)) ⟩
  mconcat (concat (map (map snd ∘ bind-helper f) da))
    ≡⟨ cong mconcat (map-concatmap-swap-lem snd (bind-helper f) da) ⟩
  mconcat (map snd (concatMap (bind-helper f) da))
    ≡⟨ refl ⟩
  mconcat (map snd (da >>= f))
    ≡⟨ refl ⟩
  totalProbability (da >>= f)
  ∎


-}
