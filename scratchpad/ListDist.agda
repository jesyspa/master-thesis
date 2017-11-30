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
