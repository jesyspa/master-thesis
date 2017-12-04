{-# OPTIONS --allow-unsolved-metas #-}
module ListDist where

open import MyPrelude
open import ListLemmas
open import NatLemmas
open import RationalLemmas

Dist : Set → Set
Dist A = List (A × Rational)

return : ∀{A} → A → Dist A
return a = [ a , one ]

bind-helper-2 : {B : Set} → Rational → B × Rational → B × Rational 
bind-helper-2 p (b , q) = b , p * q

bind-helper : {A B : Set} → (A → Dist B) → A × Rational → List (B × Rational)
bind-helper {A} {B} f (a , p) = map (bind-helper-2 p) $ f a

_>>=_ : ∀{A B} → Dist A → (A → Dist B) → Dist B
_>>=_ {A} {B} xs f = concatMap (bind-helper f) xs

bh2-id-lem2 : {B : Set} → {bq : B × Rational} → bind-helper-2 one bq ≡ bq 
bh2-id-lem2 {B} {(b , q)} =
  bind-helper-2 one (b , q)
    ≡⟨ refl ⟩
  b , one * q
    ≡⟨ cong (λ x → b , x) rat-one-lem ⟩
  (b , q)
  ∎
    
Dist-right-id : ∀{A B} → {a : A} → {f : A → Dist B} → return a >>= f ≡ f a
Dist-right-id {A} {B} {a} {f} =
  (return a >>= f)
    ≡⟨ refl ⟩
  ([ a , one ] >>= f)
    ≡⟨ refl ⟩
  concatMap (bind-helper f) [ a , one ]
    ≡⟨ refl ⟩
  (concat ∘ map (bind-helper f)) [ a , one ]
    ≡⟨ refl ⟩
  concat (map (bind-helper f) ([ a , one ]))
    ≡⟨ refl ⟩
  concat (bind-helper f (a , one) ∷ []) 
    ≡⟨ refl ⟩
  bind-helper f (a , one) ++ []
    ≡⟨ right-append-lem ⟩
  bind-helper f (a , one)
    ≡⟨ refl ⟩
  map (bind-helper-2 one) (f a)
    ≡⟨ map-weak-id-lem bh2-id-lem2 ⟩
  f a 
  ∎

uniform : (n : Nat) → Dist (Fin (suc n))
uniform n = map (λ x → x , 1 :/ suc n) fins

totalProbability : ∀{A} → Dist A → Rational
totalProbability = sum ∘ map snd

IsDist : ∀{A} → Dist A → Set
IsDist xs = totalProbability xs ≡ one 

uniform-special : totalProbability (uniform 0) ≡ one
uniform-special =
  sum (map snd [ (zero , 1 :/ 1) ])
    ≡⟨ refl ⟩
  sum [ 1 :/ 1 ]
    ≡⟨ refl ⟩
  1 :/ 1 + zro
    ≡⟨ refl ⟩
  one
  ∎

uniform-snd-lem : ∀{n} → map snd (uniform n) ≡ replicate (suc n) (1 :/ suc n)
uniform-snd-lem = {!!}

replicate-mul-lem : (n k : Nat) → sum (replicate k (1 :/ suc n)) ≡ k :/ suc n
replicate-mul-lem n zero =
  sum (replicate 0 (1 :/ suc n))
    ≡⟨ refl ⟩
  sum []
    ≡⟨ refl ⟩
  zro
    ≡⟨ sym zero-over-k-lem ⟩
  zero :/ suc n
  ∎
replicate-mul-lem n (suc k) =
  sum (replicate (suc k) (1 :/ suc n))
    ≡⟨ refl ⟩
  sum ((1 :/ suc n) ∷ replicate k (1 :/ suc n))
    ≡⟨ refl ⟩
  1 :/ suc n + sum (replicate k (1 :/ suc n))
    ≡⟨ cong (λ x → 1 :/ suc n + x) (replicate-mul-lem n k) ⟩
  1 :/ suc n + k :/ suc n
    ≡⟨ common-denom-lem 1 k (suc n) ⟩
  suc k :/ suc n
  ∎

uniform-lem : ∀{n} → totalProbability (uniform n) ≡ one
uniform-lem {n} =
  sum (map snd (uniform n))
    ≡⟨ cong sum (uniform-snd-lem {n}) ⟩
  sum (replicate (suc n) (1 :/ suc n))
    ≡⟨ replicate-mul-lem n (suc n) ⟩
  suc n :/ suc n
    ≡⟨ k-over-k-lem ⟩
  one
  ∎

uniformIsDist : ∀{n} → IsDist (uniform n)
uniformIsDist {n} = {!!}
