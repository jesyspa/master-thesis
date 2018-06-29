module Utility.Vector.Props where

open import ThesisPrelude hiding (List)
open import Utility.Vector.Functions
open import Algebra.Function
open import Utility.Num

componentwise-equality : ∀ {A : Set} {n : Nat} (x y : A) (xs ys : Vec A n)
                       → Dec (x ≡ y) → Dec (xs ≡ ys)
                       → Dec (_≡_ {A = Vec A (suc n)} (x ∷ xs) (y ∷ ys))
componentwise-equality x .x xs .xs (yes refl) (yes refl) = yes refl
componentwise-equality x y xs ys (no ph) _ = no λ p → ph (vcons-inj-head p)
componentwise-equality x y xs ys _ (no  pt) = no λ p → pt (vcons-inj-tail p)

vec-eq : ∀{A : Set} {{_ : Eq A}} {n} → (xs ys : Vec A n) → Dec (xs ≡ ys)
vec-eq [] [] = yes refl
vec-eq (x ∷ xs) (y ∷ ys) = componentwise-equality x y xs ys (x == y) (xs == ys) 

head1-Inj : ∀{l} {A : Set l} → Injective (head1 {l} {A})
head1-Inj {x = x ∷ []} {y = .x ∷ []} refl = refl

head-nattrans : ∀{l n} {A B : Set l} → (f : A → B)
              → (xs : Vec A (suc n))
              → f (head xs) ≡ head (fmap f xs)
head-nattrans f (x ∷ _) = refl

fmap-ext-vec : ∀{l n} {A B : Set l} (f g : A → B)
             → (∀ a → f a ≡ g a)
             → (xs : Vec A n)
             → fmap f xs ≡ fmap g xs
fmap-ext-vec f g pf [] = refl
fmap-ext-vec f g pf (x ∷ xs) rewrite sym (fmap-ext-vec f g pf xs) | pf x = refl

fmap-id-vec : ∀{l n} {A : Set l} → (xs : Vec A n) → xs ≡ fmap id xs
fmap-id-vec [] = refl
fmap-id-vec (x ∷ xs) rewrite sym (fmap-id-vec xs) = refl

fmap-comp-vec : ∀{l n} {A B C : Set l} (g : B → C) (f : A → B) (xs : Vec A n) 
              → fmap (g ∘′ f) xs ≡ fmap g (fmap f xs)
fmap-comp-vec g f [] = refl
fmap-comp-vec g f (x ∷ xs) rewrite sym (fmap-comp-vec g f xs) = refl

module _ {l : Level} {n : Nat} where
  open import Algebra.FunctorProps (λ τ → Vec {l} τ n)
  instance
    FunctorPropsVec : FunctorProps
    FunctorPropsVec = record { fmap-ext = fmap-ext-vec ; fmap-id = fmap-id-vec ; fmap-comp = fmap-comp-vec }

vtake-vconcat-inv : ∀{l}{A : Set l}{n k}(v : Vec A n)(w : Vec A k)
                  → v ≡ vtake n (vconcat v w)
vtake-vconcat-inv [] w = refl
vtake-vconcat-inv (x ∷ v) w rewrite sym (vtake-vconcat-inv v w) = refl

vsplit-vconcat-invˡ : ∀{l}{A : Set l}{n k}(v : Vec A n)(w : Vec A k)
                   → v ≡ let l , r = vsplit n (vconcat v w) in l
vsplit-vconcat-invˡ [] w = refl
vsplit-vconcat-invˡ (x ∷ v) w rewrite sym (vsplit-vconcat-invˡ v w) = refl

vsplit-vconcat-invʳ : ∀{l}{A : Set l}{n k}(v : Vec A n)(w : Vec A k)
                   → w ≡ let l , r = vsplit n (vconcat v w) in r
vsplit-vconcat-invʳ [] w = refl
vsplit-vconcat-invʳ (x ∷ v) w rewrite sym (vsplit-vconcat-invʳ v w) = refl

postulate
  vsplit-vtake-fst : ∀{l}{A : Set l} n j k
                   → (v : Vec A (n + j + k))
                   → (eq : n + j + k ≡ (n + (j + k)))
                   → fst (vsplit n (transport (Vec A) eq v)) ≡ fst (vsplit n (vtake  (n + j) {k = k} v))
