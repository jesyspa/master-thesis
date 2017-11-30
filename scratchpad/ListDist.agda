module ListDist where

open import MyPrelude

data Dist (A : Set) : Set where
  dist : List (A × Rational) → Dist A

getDist : ∀{A} → Dist A → List (A × Rational)
getDist (dist x) = x

return : ∀{A} → A → Dist A
return a = dist [ a , mkratio 1 1 ]

_>>=_ : ∀{A B} → Dist A → (A → Dist B) → Dist B
_>>=_ {A} {B} (dist xs) f = dist $ concatMap g xs
  where
  g : A × Rational → List (B × Rational)
  g (a , p) = map (λ { (b , q) → b , p *Q q }) $ getDist $ f a




{-
data Dist (A : Set) : Set where
  dist : List (A × ℚ) → Dist A

return : ∀{A} → A → Dist A
return a = dist [ a , ((+ 1) ÷ 1) ]

mul : ℚ → ℚ → ℚ
mul a b = (ℚ.numerator a Data.Integer.* ℚ.numerator b) ÷ (ℕ.suc (ℚ.denominator-1 a) Data.Nat.* ℕ.suc (ℚ.denominator-1 b))

_>>=_ : ∀{A B} → Dist A → (A → Dist B) → Dist B
_>>=_ {A} {B} (dist x) f = dist (concatMap g x)
  where
  g : A × ℚ → List (B × ℚ)
  g (a , p) with f a
  ...          | dist bs = Data.List.map h bs
    where
    h : B × ℚ → B × ℚ
    h (b , q) = b , mul p q

-}
