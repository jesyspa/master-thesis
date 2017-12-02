module ContDist where

open import MyPrelude

Dist : Set → Set
Dist A = (A → Rational) → Rational

return : ∀{A} → A → Dist A
return a = λ x → x a

_>>=_ : ∀{A B} → Dist A → (A → Dist B) → Dist B
d >>= f = λ bc → d λ a → f a bc

right-lem : ∀{A B} → {f : A → Dist B} → {a : A} → (return a >>= f) ≡ f a
right-lem = refl

left-lem : ∀{A} → {da : Dist A} → (da >>= return) ≡ da
left-lem = refl

assoc-lem : ∀{A B C} → {da : Dist A} → {fb : A → Dist B} → {fc : B → Dist C} → (da >>= fb) >>= fc ≡ da >>= (λ x → (fb x >>= fc))
assoc-lem = refl

uniform : ∀ n → Dist (Fin (suc n))
uniform n = λ f → sum (map f fins)

