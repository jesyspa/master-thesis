module MonoidLemmas where

open import MyPrelude
open import Monoid

mconcat-empty-lem : ∀{A}
                  → {{M : Monoid A}}
                  → mempty {{M}} ≡ mconcat {{M}} []
mconcat-empty-lem = refl

mconcat-append-lem : ∀{A}
                   → {{M : Monoid A}}
                   → (xs ys : List A)
                   → mconcat (xs ++ ys) ≡ mconcat xs <> mconcat ys
mconcat-append-lem {{M}} [] ys rewrite sym (mconcat-empty-lem {{M}}) = left-identity {{M}} (mconcat {{M}} ys)
mconcat-append-lem {{M}} (x ∷ xs) ys =
  x <> mconcat (xs ++ ys)
    ≡⟨ cong (λ e → x <> e) (mconcat-append-lem xs ys) ⟩
  x <> (mconcat xs <> mconcat ys)
    ≡⟨ assoc {{M}} x (mconcat xs) (mconcat ys) ⟩
  (x <> mconcat xs) <> mconcat ys
  ∎

mconcat-concat-swap-lem : ∀{A : Set}
                      → {{M : Monoid A}}
                      → (xss : List (List A))
                      → mconcat (concat xss) ≡ mconcat (map mconcat xss)
mconcat-concat-swap-lem [] = refl
mconcat-concat-swap-lem (xs ∷ xss) =
  mconcat (xs ++ concat xss)
    ≡⟨ mconcat-append-lem xs (concat xss) ⟩
  mconcat xs <> mconcat (concat xss)
    ≡⟨ cong (λ e → mconcat xs <> e) (mconcat-concat-swap-lem xss) ⟩
  mconcat xs <> mconcat (map mconcat xss)
    ≡⟨ refl ⟩
  mconcat (mconcat xs ∷ map mconcat xss)
  ∎
