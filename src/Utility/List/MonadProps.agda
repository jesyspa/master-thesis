module Utility.List.MonadProps where

open import ThesisPrelude
open import Algebra.Monoid
open import Algebra.Function
open import Utility.List.MonoidProps
open import Utility.List.ComplexProps
open import Utility.List.FunctorProps
open import Utility.List.ApplicativeProps

list->>=-assoc : ∀{l} {A B C : Set l} → (xs : List A) → (f : A → List B) → (g : B → List C)
               → (xs >>= f >>= g) ≡ (xs >>= (λ y → f y >>= g))
list->>=-assoc xs f g =
  concat (map g (concat (map f xs)))
    ≡⟨ cong concat (map-concatmap-swap g f xs) ⟩
  concat (concat (map (map g ∘′ f) xs))
    ≡⟨ map-concat-swap (map g ∘′ f) xs ⟩ʳ
  concat (map (concat ∘′ map g ∘′ f) xs)
  ∎

list-return->>=-right-id : ∀{l} {A : Set l} → (xs : List A) → xs ≡ (xs >>= [_])
list-return->>=-right-id = concat-retraction

list-return->>=-left-id  : ∀{l} {A B : Set l} → (x : A) → (f : A → List B) → ([ x ] >>= f) ≡ f x
list-return->>=-left-id x f = sym (list-++-right-identity (f x))

list-<*>-is-ap : ∀{l} {A B : Set l} (xs : List (A → B)) (ys : List A) → (xs <*> ys) ≡ (xs >>= λ x → ys >>= λ y → [ x y ])
list-<*>-is-ap xs ys = cong concat (map-ext (λ z → map z ys) (λ x → concatMap (λ y → [ x y ]) ys) eq xs)
  where eq : ∀ a → map a ys ≡ concatMap (λ y → a y ∷ []) ys
        eq a =
           map a ys
             ≡⟨ concat-retraction (map a ys) ⟩
           concat (map (λ y → [ y ]) (map a ys))
             ≡⟨ cong concat (map-comp (λ z → z ∷ []) a ys) ⟩ʳ
           concat (map (λ y → a y ∷ []) ys)
           ∎

list->>=-ext : ∀{l} {A B : Set l} (xs : List A) (f g : A → List B)
             → (∀ x → f x ≡ g x)
             → concat (map f xs) ≡ concat (map g xs)
list->>=-ext xs f g pf = cong concat (map-ext f g pf xs)

module _ {l : Level} where
  open import Algebra.MonadProps (List {l}) using (MonadProps)
  instance
    MonadPropsList : MonadProps
    MonadPropsList = record
                       { >>=-assoc = list->>=-assoc
                       ; return->>=-right-id = list-return->>=-right-id
                       ; return->>=-left-id = list-return->>=-left-id
                       ; >>=-ext = list->>=-ext
                       ; <*>-is-ap = list-<*>-is-ap
                       }
