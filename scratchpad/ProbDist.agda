{-# OPTIONS --allow-unsolved-metas #-}
module ProbDist where

open import MyPrelude
open import ListLemmas
open import NatLemmas
open import BitProbability
open import Monoid
open import MonoidInstances
open import MonoidLemmas

Dist : Set → Set
Dist A = List (A × Prob)

return : ∀{A} → A → Dist A
return a = [ a , always ]

bind-helper-2 : {B : Set} → Prob → B × Prob → B × Prob 
bind-helper-2 p (b , q) = b , p *P q

bind-helper : {A B : Set} → (A → Dist B) → A × Prob → List (B × Prob)
bind-helper {A} {B} f (a , p) = map (bind-helper-2 p) $ f a

_>>=_ : ∀{A B} → Dist A → (A → Dist B) → Dist B
_>>=_ {A} {B} xs f = concatMap (bind-helper f) xs

bh2-id-lem2 : {B : Set} → (bq : B × Prob) → bq ≡ bind-helper-2 always bq
bh2-id-lem2 (b , q) = refl
    
Dist-right-id : ∀{A B} → {a : A} → {f : A → Dist B} → f a ≡ return a >>= f
Dist-right-id {A} {B} {a} {f} =
  f a
    ≡⟨ map-weak-id-lem (bind-helper-2 always) (f a) bh2-id-lem2 ⟩
  map (bind-helper-2 always) (f a)
    ≡⟨ right-append-lem ⟩
  map (bind-helper-2 always) (f a) ++ []
    ≡⟨ refl ⟩
  concat [ map (bind-helper-2 always) (f a) ]
    ≡⟨ refl ⟩
  concatMap (bind-helper f) [ a , always ]
  ∎

totalProbability : ∀{A} → Dist A → Prob
totalProbability = mconcat {{MonoidProbPlus}} ∘ map snd

IsDist : ∀{A} → Dist A → Set
IsDist xs = always ≡ totalProbability xs

coin : Dist Bool
coin = (false , sometimes halfway) ∷ (true , sometimes halfway) ∷ []

uniformVec : (n : Nat) → Dist (Vec Bool n)
uniformVec zero = return []
uniformVec (suc n) = coin >>= λ c → uniformVec n >>= λ v → return (c ∷ v)

Dist-coin : IsDist coin
Dist-coin = refl

Dist-return : ∀{A} → (a : A) → IsDist (return a)
Dist-return a = refl

Dist-bind-helper-4 : (p : Prob) → (xs : List Prob)
                   → p *P mconcat xs ≡ mconcat (map (_*P_ p) xs)
Dist-bind-helper-4 p [] rewrite sym (mconcat-empty-lem {{MonoidProbPlus}}) = sym (never-right-mul-zero-lem p)
Dist-bind-helper-4 p (x ∷ xs) =
  p *P (x <> mconcat xs)
    ≡⟨ {!!} ⟩ -- oops, this can't be proven. bugger.
  p *P x <> (p *P mconcat xs)
    ≡⟨ cong (λ e → p *P x <> e) (Dist-bind-helper-4 p xs) ⟩
  p *P x <> mconcat (map (_*P_ p) xs)
  ∎

-- bind-helper-2 p (b , q) = b , p *P q
Dist-bind-helper-3 : ∀{B} → (p : Prob) → (x : B × Prob)
                   → (_*P_ p ∘ snd) x ≡ snd (bind-helper-2 p x)
Dist-bind-helper-3 p (b , q) = refl 

Dist-bind-helper-2 : ∀{A B} → (f : A → Dist B) → (a : A) → (p : Prob)
                   → IsDist (f a) 
                   → p ≡ mconcat (map snd (bind-helper f (a , p)))
Dist-bind-helper-2 f a p pf =
  p
    ≡⟨ always-right-mul-unit-lem p ⟩
  p *P always
    ≡⟨ cong (_*P_ p) pf ⟩
  p *P mconcat (map snd (f a))
    ≡⟨ Dist-bind-helper-4 p (map snd (f a)) ⟩
  mconcat (map (_*P_ p) (map snd (f a)))
    ≡⟨ cong mconcat (sym (map-compose-lem (_*P_ p) snd (f a))) ⟩
  mconcat (map (_*P_ p ∘ snd) (f a))
    ≡⟨ cong mconcat (map-equiv-lem (_*P_ p ∘ snd) (snd ∘ bind-helper-2 p) (f a) (Dist-bind-helper-3 p)) ⟩
  mconcat (map (snd ∘ bind-helper-2 p) (f a))
    ≡⟨ cong mconcat (map-compose-lem snd (bind-helper-2 p) (f a)) ⟩
  mconcat (map snd (map (bind-helper-2 p) (f a)))
  ∎

Dist-bind : ∀{A B} → (da : Dist A) → (f : A → Dist B)
          → IsDist da
          → ((a' : A) → IsDist (f a'))
          → IsDist (da >>= f)
Dist-bind da f pda pf =
  always
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

Dist-uniformVec : (n : Nat) → IsDist (uniformVec n)
Dist-uniformVec zero = refl
Dist-uniformVec (suc n) = {!!}
