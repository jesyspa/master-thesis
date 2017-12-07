{-# OPTIONS --allow-unsolved-metas #-}
module ListDist where

open import MyPrelude
open import ListLemmas
open import NatLemmas
open import BitProbability

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

bh2-id-lem2 : {B : Set} → {bq : B × Prob} → bind-helper-2 always bq ≡ bq 
bh2-id-lem2 {B} {(b , q)} = ?
    
Dist-right-id : ∀{A B} → {a : A} → {f : A → Dist B} → return a >>= f ≡ f a
Dist-right-id {A} {B} {a} {f} = ?

totalProbability : ∀{A} → Dist A → Prob
totalProbability = sum ∘ map snd

IsDist : ∀{A} → Dist A → Set
IsDist xs = totalProbability xs ≡ one 

