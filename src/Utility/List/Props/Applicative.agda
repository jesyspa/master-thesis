module Utility.List.Props.Applicative where

open import ThesisPrelude
open import Utility.List.Props.Functor
open import Utility.List.Props.Monoid
open import Utility.List.Props.Complex

list-<*>-composition-head : ∀{l} {A B C : Set l} (x : B → C) (ys : List (A → B)) (zs : List A)
                          → map x (concat (map (λ f → map f zs) ys))
                          ≡ concat (map (λ y → map y zs) (map (_∘′_ x) ys))
list-<*>-composition-head x ys zs =
  map x (concat (map (λ y → map y zs) ys))
    ≡⟨ map-concatmap-swap x (λ y → map y zs) ys ⟩
  concat (map (λ y → map x (map y zs)) ys)
    ≡⟨ cong concat (map-ext (λ y → map x (map y zs)) (λ y → map (x ∘′ y) zs) (λ a → sym (map-comp x a zs)) ys) ⟩
  concat (map (λ y → map (x ∘′ y) zs) ys)
    ≡⟨ cong concat (map-comp (λ y → map y zs) (_∘′_ x) ys) ⟩
  concat (map (λ y → map y zs) (map (_∘′_ x) ys))
  ∎

list-<*>-composition-tail : ∀{l} {A B C : Set l} (xs : List (B → C)) (ys : List (A → B)) (zs : List A)
                          → concat (map (λ x → map x (concat (map (λ y → map y zs) ys))) xs)
                          ≡ concat (map (λ z → map z zs) (concat (map (λ x → map x ys) (map _∘′_ xs))))
list-<*>-composition-tail xs ys zs =
  concat (map (λ x → map x (concat (map (λ y → map y zs) ys))) xs)
    ≡⟨ cong concat
            (map-ext (λ x → map x (concat (map (λ y → map y zs) ys)))
                     (λ x → concat (map (λ y → map x (map y zs)) ys))
                     (λ x → map-concatmap-swap x (λ y → map y zs) ys) xs) ⟩
  concat (map (λ x → concat (map (λ y → map x (map y zs)) ys)) xs)
    ≡⟨ map-concat-swap (λ x → map (λ y → map x (map y zs)) ys) xs ⟩
  concat (concat (map (λ x → map (λ y → map x (map y zs)) ys) xs))
    ≡⟨ cong (λ e → concat (concat e))
       (map-ext (λ x → map (λ z → map x (map z zs)) ys)
                ((map (λ y → map y zs)) ∘′ (λ x → map (_∘′_ x) ys))
                (λ a →
                  map (λ y → map a (map y zs)) ys
                    ≡⟨ map-ext (λ y → map a (map y zs)) (λ y → map (a ∘′ y) zs) (λ a₁ → sym (map-comp a a₁ zs)) ys ⟩
                  map (λ y → map (a ∘′ y) zs) ys
                    ≡⟨ map-comp (λ y → map y zs) (_∘′_ a) ys ⟩
                  map (λ y → map y zs) (map (_∘′_ a) ys)
                  ∎)
                xs) ⟩
  concat (concat (map (map (λ f → map f zs) ∘′ (λ x → map (_∘′_ x) ys)) xs))
    ≡⟨ cong concat (map-concatmap-swap (λ y → map y zs) (λ x → map (_∘′_ x) ys) xs) ⟩ʳ
  concat (map (λ f → map f zs) (concat (map (λ x → map (_∘′_ x) ys) xs)))
    ≡⟨ cong (λ e → concat (map (λ f → map f zs) (concat e))) (map-comp (λ x → map x ys) _∘′_ xs) ⟩
  concat (map (λ f → map f zs) (concat (map (λ x → map x ys) (map _∘′_ xs))))
  ∎

list-<*>-composition : ∀{l} {A B C : Set l} (xs : List (B → C)) (ys : List (A → B)) (zs : List A)
                     → (xs <*> (ys <*> zs)) ≡ ([ _∘′_ ] <*> xs <*> ys <*> zs)
list-<*>-composition [] ys zs = refl
list-<*>-composition (x ∷ xs) ys zs
  rewrite sym (list-<*>-composition xs ys zs) =
  map x (concat (map (λ f → map f zs) ys)) ++ concat (map (λ f → map f (concat (map (λ g → map g zs) ys))) xs)
    ≡⟨ cong₂ (λ e f → e ++ f) 
             (list-<*>-composition-head x ys zs)
             (list-<*>-composition-tail xs ys zs)⟩
  concat (map (λ z → map z zs) (map (_∘′_ x) ys)) ++ concat (map (λ z → map z zs) (concat (map (λ z → map z ys) (map _∘′_ xs))))
    ≡⟨ cong (λ e → concat (map (λ z → map z zs) (map (_∘′_ x) ys))
                          ++ concat (map (λ z → map z zs) (concat (map (λ z → map z ys) e))))
            (list-++-right-identity (map _∘′_ xs)) ⟩
  concat (map (λ z → map z zs) (map (_∘′_ x) ys)) ++ concat (map (λ z → map z zs) (concat (map (λ z → map z ys) (map _∘′_ xs ++ []))))
    ≡⟨ concat-append-dist (map (λ z → map z zs) (map (_∘′_ x) ys))
                          (map (λ z → map z zs) (concat (map (λ z → map z ys) (map _∘′_ xs ++ [])))) ⟩ʳ
  concat (map (λ z → map z zs) (map (_∘′_ x) ys) ++ map (λ z → map z zs) (concat (map (λ z → map z ys) (map _∘′_ xs ++ []))))
    ≡⟨ cong concat (map-append-dist (λ z → map z zs) (map (_∘′_ x) ys) (concat (map (λ z → map z ys) (map _∘′_ xs ++ [])))) ⟩ʳ
  concat (map (λ z → map z zs) (map (_∘′_ x) ys ++ concat (map (λ z → map z ys) (map _∘′_ xs ++ []))))
  ∎

list-<*>-homomorphism : ∀{l} {A B : Set l} (f : A → B) (x : A)
                      → [ f x ] ≡ ([ f ] <*> [ x ])
list-<*>-homomorphism f x = refl

list-<*>-interchange : ∀{l} {A B : Set l} (xs : List (A → B)) (y : A)
                     → (xs <*> [ y ]) ≡ ([ (λ f → f y) ] <*> xs)
list-<*>-interchange  xs y =
  concatMap (λ f → f y ∷ []) xs
    ≡⟨ cong concat (map-comp (λ x → x ∷ []) (λ f → f y) xs) ⟩
  concat(map (λ x → x ∷ []) (map (λ f → f y) xs))
    ≡⟨ concat-retraction (map (λ f → f y) xs) ⟩ʳ
  map (λ f → f y) xs
    ≡⟨ list-++-right-identity (map (λ f → f y) xs) ⟩
  map (λ f → f y) xs ++ []
  ∎

list-fmap-is-pure-<*> : ∀{l} {A B : Set l} (f : A → B) (xs : List A)
                      → fmap f xs ≡ ([ f ] <*> xs)
list-fmap-is-pure-<*> f xs rewrite sym (list-++-right-identity (fmap f xs)) = refl

module _ {l : Level} where
  open import Algebra.ApplicativeProps (List {l}) using (ApplicativeProps)
  instance
    ApplicativePropsList : ApplicativeProps
    ApplicativePropsList = record
                             { <*>-composition = list-<*>-composition
                             ; <*>-homomorphism = list-<*>-homomorphism
                             ; <*>-interchange = list-<*>-interchange
                             ; fmap-is-pure-<*> = list-fmap-is-pure-<*>
                             }
