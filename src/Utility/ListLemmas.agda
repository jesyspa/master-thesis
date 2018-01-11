{-# OPTIONS --allow-unsolved-metas #-}
module Utility.ListLemmas where

open import ThesisPrelude
open import Algebra.Monoid
open import Algebra.Function

∷-list-Inj : ∀{l} {A : Set l} (x : A)
        → Injective (List._∷_ {A = A} x)
∷-list-Inj x refl = refl

list-++-assoc : ∀{l} {A : Set l} → (xs ys zs : List A) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs 
list-++-assoc [] ys zs = refl
list-++-assoc (x ∷ xs) ys zs rewrite list-++-assoc xs ys zs = refl

list-++-right-identity : ∀{l} {A : Set l} → (xs : List A) → xs ≡ xs ++ []
list-++-right-identity [] = refl
list-++-right-identity (x ∷ xs) rewrite sym (list-++-right-identity xs) = refl

instance
  MonoidPropsList : ∀{l} {A : Set l} → MonoidProps (List A)
  MonoidPropsList = record { op-assoc = list-++-assoc ; unit-left = λ a → refl ; unit-right = list-++-right-identity }

map-ext : ∀{l l′} {A : Set l} {B : Set l′}
        → (f g : A → B)
        → (∀ a → f a ≡ g a)
        → (xs : List A)
        → map f xs ≡ map g xs
map-ext f g p [] = refl
map-ext f g p (x ∷ xs) rewrite map-ext f g p xs | p x = refl

map-id : ∀{l} {A : Set l}
       → (xs : List A)
       → xs ≡ map id xs
map-id [] = refl
map-id (x ∷ xs) rewrite sym (map-id xs) = refl

map-comp : ∀{l l′ l′′} {A : Set l} {B : Set l′} {C : Set l′′} (g : B → C) (f : A → B) (xs : List A)
         → map (g ∘′ f) xs ≡ map g (map f xs)
map-comp g f [] = refl
map-comp g f (x ∷ xs) rewrite sym (map-comp g f xs) = refl

map-append-dist : ∀{l l′} {A : Set l} {B : Set l′}
                → (f : A → B)
                → (xs ys : List A)
                → map f (xs ++ ys) ≡ map f xs ++ map f ys 
map-append-dist f [] ys = refl
map-append-dist f (x ∷ xs) ys rewrite sym (map-append-dist f xs ys) = refl

filter-append-dist : ∀{l} {A : Set l}
                   → (p : A → Bool)
                   → (xs ys : List A)
                   → filter p (xs ++ ys) ≡ filter p xs ++ filter p ys 
filter-append-dist p [] ys = refl
filter-append-dist p (x ∷ xs) ys with p x
... | false = filter-append-dist p xs ys
... | true = cong (_∷_ x) (filter-append-dist p xs ys)

{-# DISPLAY foldr _++_ List.[] = concat #-}

concat-append-dist : ∀{l} {A : Set l}
                   → (xs ys : List (List A))
                   → concat (xs ++ ys) ≡ concat xs ++ concat ys 
concat-append-dist [] ys = refl
concat-append-dist (x ∷ xs) ys rewrite concat-append-dist xs ys = op-assoc x (concat xs) (concat ys)

concat-retraction : ∀{l} {A : Set l}
                  → Retraction concat {A = A} of map (λ x → x ∷ [])
concat-retraction [] = refl
concat-retraction (x ∷ xs) rewrite sym (concat-retraction xs) = refl

map-concatmap-swap : ∀{l} {A B C : Set l}
                   → (f : B → C) → (g : A → List B) 
                   → (xs : List A)
                   → map f (concatMap g xs) ≡ concatMap (map f ∘ g) xs
map-concatmap-swap f g [] = refl
map-concatmap-swap f g (x ∷ xs) rewrite sym (map-concatmap-swap f g xs) = map-append-dist f (g x) (concatMap g xs)

map-concat-swap : ∀{l} {A B : Set l}
                → (f : A → List (List B))
                → (xs : List A)
                → concat (map (concat ∘′ f) xs) ≡ concat (concat (map f xs))
map-concat-swap f [] = refl
map-concat-swap f (x ∷ xs) rewrite map-concat-swap f xs | concat-append-dist (f x) (concat (map f xs)) = refl

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

--                   → map f (concatMap g xs) ≡ concatMap (map f ∘ g) xs
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

open import Algebra.FunctorProps List using (FunctorProps)
open import Algebra.ApplicativeProps List using (ApplicativeProps)
open import Algebra.MonadProps List using (MonadProps)
instance
  FunctorPropsList : FunctorProps
  FunctorPropsList = record { fmap-ext = map-ext ; fmap-id = map-id ; fmap-comp = map-comp }

  ApplicativePropsList : ApplicativeProps
  ApplicativePropsList = record
                           { <*>-composition = list-<*>-composition
                           ; <*>-homomorphism = list-<*>-homomorphism
                           ; <*>-interchange = list-<*>-interchange
                           ; fmap-is-pure-<*> = list-fmap-is-pure-<*>
                           ; fprops = FunctorPropsList
                           }

  MonadPropsList : MonadProps
  MonadPropsList = record
                     { >>=-assoc = list->>=-assoc
                     ; return->>=-right-id = list-return->>=-right-id
                     ; return->>=-left-id = list-return->>=-left-id
                     ; <*>-is-ap = list-<*>-is-ap
                     ; aprops = ApplicativePropsList
                     }

map-ext-id : ∀{l} {A : Set l} (f : A → A) → (∀ a → a ≡ f a) → (xs : List A)
           → xs ≡ map f xs
map-ext-id = FunctorProps.fmap-ext-id FunctorPropsList

map-lift-ret : ∀{l} {A B : Set l} (g : B → A) (f : A → B)
             → Retraction g of f
             → Retraction map g of map f
map-lift-ret = FunctorProps.fmap-lift-ret FunctorPropsList


filter-reduction-identity : ∀{l} {A B : Set l} (g : B → A) (f : A → B) (p : A → Bool) (xs : List A)
                          → Retraction g of f
                          → map f (filter p xs) ≡ filter (p ∘ g) (map f xs)
filter-reduction-identity g f p [] pr = refl
filter-reduction-identity g f p (x ∷ xs) pr rewrite sym (pr x) with p x
... | false rewrite sym (filter-reduction-identity g f p xs pr) = refl
... | true rewrite sym (filter-reduction-identity g f p xs pr) = refl
