module Utility.Elem where

open import ThesisPrelude
open import Utility.ListLemmas
open import Algebra.Function
open import Algebra.ExactSize

infix 4 _∈_
data _∈_ {l} {A : Set l} : A → List A → Set l where
  here : ∀ x xs → x ∈ (x ∷ xs)
  there : ∀ x y xs → x ∈ xs → x ∈ (y ∷ xs)
  
module _ {l} {A : Set l} where
  there-Inj : ∀{x y : A} {xs : List A}
            → Injective (there x y xs)
  there-Inj refl = refl
  
  in-++-left : ∀ {a : A} (xs ys : List A)
             → a ∈ xs
             → a ∈ (xs ++ ys)
  in-++-left .(a ∷ xs) ys (here a xs) = here a (xs ++ ys)
  in-++-left .(y ∷ xs) ys (there a y xs p) = there a y (xs ++ ys) (in-++-left xs ys p)
  
  in-++-left-Inj : ∀{a : A} (xs ys : List A)
                 → Injective (in-++-left {a = a} xs ys)
  in-++-left-Inj [] ys {()}
  in-++-left-Inj (a ∷ xs) ys {here .a .xs} {here .a .xs} pe = refl
  in-++-left-Inj (a ∷ xs) ys {here .a .xs} {there .a .a .xs pb} ()
  in-++-left-Inj (a ∷ xs) ys {there .a .a .xs pa} {here .a .xs} ()
  in-++-left-Inj (x ∷ xs) ys {there a .x .xs pa} {there .a .x .xs pb} pe
    rewrite in-++-left-Inj xs ys (there-Inj pe) = refl
  
  in-++-right : ∀ {a : A} (xs ys : List A)
              → a ∈ ys
              → a ∈ (xs ++ ys)
  in-++-right [] ys p = p
  in-++-right {a = a} (x ∷ xs) ys p = there a x (xs ++ ys) (in-++-right xs ys p)
  
  in-some-++ : ∀{a : A} (xs ys : List A)
             → a ∈ (xs ++ ys)
             → Either (a ∈ xs) (a ∈ ys)
  in-some-++ [] ys p = right p
  in-some-++ (a ∷ xs) ys (here .a .(xs ++ ys)) = left (here a xs)
  in-some-++ (y ∷ xs) ys (there a .y .(xs ++ ys) p) with in-some-++ xs ys p
  in-some-++ (y ∷ xs) ys (there a .y .(xs ++ ys) p) | left pl = left (there a y xs pl)
  in-some-++ (y ∷ xs) ys (there a .y .(xs ++ ys) p) | right pr = right pr
  
  in-some-++-left : ∀(a : A) (xs ys : List A)
                  → (p : a ∈ xs)
                  → left p ≡ in-some-++ xs ys (in-++-left xs ys p)
  in-some-++-left a [] ys ()
  in-some-++-left a (.a ∷ xs) ys (here .a .xs) = refl
  in-some-++-left a (x ∷ xs) ys (there .a .x .xs p)
    rewrite sym (in-some-++-left a xs ys p) = refl
  
  in-some-++-right : ∀(a : A) (xs ys : List A)
                  → (p : a ∈ ys)
                  → right p ≡ in-some-++ xs ys (in-++-right xs ys p)
  in-some-++-right a [] ys p = refl
  in-some-++-right a (x ∷ xs) ys p rewrite sym (in-some-++-right a xs ys p) = refl
  
  in-some-++-Inj : ∀{a : A} (xs ys : List A)
                 → Injective (in-some-++ {a = a} xs ys)
  in-some-++-Inj [] ys refl = refl
  in-some-++-Inj (a ∷ xs) ys {here .a ._} {here .a ._} pe = refl
  in-some-++-Inj (a ∷ xs) ys {here .a ._} {there .a .a ._ q} pe with in-some-++ xs ys q
  in-some-++-Inj (a ∷ xs) ys {here .a ._} {there .a .a ._ q} () | left _
  in-some-++-Inj (a ∷ xs) ys {here .a ._} {there .a .a ._ q} () | right _
  in-some-++-Inj (a ∷ xs) ys {there .a .a ._ p} {here .a ._} pe with in-some-++ xs ys p
  in-some-++-Inj (a ∷ xs) ys {there .a .a ._ p} {here .a ._} () | left _
  in-some-++-Inj (a ∷ xs) ys {there .a .a ._ p} {here .a ._} () | right _
  in-some-++-Inj (x ∷ xs) ys {there a .x ._ p} {there .a .x ._ q} pe
    with in-some-++ xs ys p | graphAt (in-some-++ xs ys) p
       | in-some-++ xs ys q | graphAt (in-some-++ xs ys) q
  in-some-++-Inj (x ∷ xs) ys {there a .x ._ p} {there .a .x ._ q} refl
       | left pl | ingraph pig
       | left .pl | ingraph qig
       rewrite in-some-++-Inj xs ys (pig ⟨≡⟩ʳ qig) = refl
  in-some-++-Inj (x ∷ xs) ys {there a .x ._ p} {there .a .x ._ q} () | left pl | ingraph pig | right qr | ingraph qig
  in-some-++-Inj (x ∷ xs) ys {there a .x ._ p} {there .a .x ._ q} () | right pl | ingraph pig | left qr | ingraph qig
  in-some-++-Inj (x ∷ xs) ys {there a .x ._ p} {there .a .x ._ q} refl
       | right pl | ingraph pig
       | right .pl | ingraph qig
       rewrite in-some-++-Inj xs ys (pig ⟨≡⟩ʳ qig) = refl
  
  neq-there : ∀(a x : A) (_ : ¬ (a ≡ x)) (xs : List A)
            → a ∈ x ∷ xs → a ∈ xs
  neq-there a .a neq xs (here .a .xs) = ⊥-elim (neq refl)
  neq-there a x neq xs (there .a .x .xs p) = p
  
  module _ {B : Set l} where
    map-preserves-in : ∀(f : A → B) (a : A) (xs : List A)
                     → a ∈ xs
                     → f a ∈ map f xs
    map-preserves-in f a .(a ∷ xs) (here .a xs) = here (f a) (map f xs)
    map-preserves-in f a .(x ∷ xs) (there .a x xs p) = there (f a) (f x) (map f xs) (map-preserves-in f a xs p)
    
    neq-there-lem : ∀(a x : A) (neq : ¬ (a ≡ x)) (xs : List A)
              → (p : a ∈ x ∷ xs)
              → p ≡ there a x xs (neq-there a x neq xs p)
    neq-there-lem a .a neq xs (here .a .xs) = ⊥-elim (neq refl)
    neq-there-lem a x neq xs (there .a .x .xs p) = refl
    
    
    drop-map-lem-helper : ∀(f : A → B) (_ : Injective f) (a : A) (xs : List A) (ys : List B)
                        → ys ≡ map f xs → f a ∈ ys
                        → a ∈ xs
    drop-map-lem-helper f pf a [] .(f a ∷ ys) () (here .(f a) ys)
    drop-map-lem-helper f pf a (x ∷ xs) .(f a ∷ ys) eq (here .(f a) ys)
      rewrite pf (cons-inj-head eq) = here x xs
    drop-map-lem-helper f pf a [] .(y ∷ ys) () (there .(f a) y ys p)
    drop-map-lem-helper f pf a (x ∷ xs) .(y ∷ ys) eq (there .(f a) y ys p) = there a x xs (drop-map-lem-helper f pf a xs ys (cons-inj-tail eq) p)
    
    drop-map-lem : ∀(f : A → B) (_ : Injective f) (a : A) (xs : List A)
                 → f a ∈ map f xs
                 → a ∈ xs
    drop-map-lem f fp a xs p = drop-map-lem-helper f fp a xs (map f xs) refl p
    
    map-preserves-Sec-helper : ∀(f : A → B) (pf : Injective f) (a : A) (xs : List A) (ys : List B)
                             → (eq : ys ≡ map f xs) → (p : f a ∈ ys)
                             → transport (λ zs → f a ∈ zs) eq p ≡ map-preserves-in f a xs (drop-map-lem-helper f pf a xs ys eq p)
    map-preserves-Sec-helper f pf a [] .(f a ∷ ys) () (here .(f a) ys)
    map-preserves-Sec-helper f pf a (x ∷ xs) ._ eq (here .(f a) ys) with pf (cons-inj-head eq) | cons-inj-tail eq
    map-preserves-Sec-helper f pf a (.a ∷ xs) ._ refl (here .(f a) .(map f xs)) | refl | refl = refl
    map-preserves-Sec-helper f pf a [] .(y ∷ ys) () (there .(f a) y ys p)
    map-preserves-Sec-helper f pf a (x ∷ xs) .(y ∷ ys) eq (there .(f a) y ys p)
      rewrite sym (map-preserves-Sec-helper f pf a xs ys (cons-inj-tail eq) p)
         with eq
    ... | refl = refl
    
    
    map-preserves-Sec : ∀(f : A → B) (fp : Injective f) (a : A) (xs : List A)
                      → Section drop-map-lem f fp a xs of map-preserves-in f a xs
    map-preserves-Sec f fp a xs p = map-preserves-Sec-helper f fp a xs (map f xs) refl p
  
  module _ {{_ : Eq A}} where
    equalFilter-fun : ∀(a : A) (xs : List A)
                    → a ∈ xs → a ∈ filter (isYes ∘ (_==_ a)) xs
    equalFilter-fun a .(a ∷ xs) (here .a xs) with a == a
    equalFilter-fun a .(a ∷ xs) (here .a xs) | yes refl = here a (filter (isYes ∘ (_==_ a)) xs)
    equalFilter-fun a .(a ∷ xs) (here .a xs) | no p = ⊥-elim (p refl)
    equalFilter-fun a .(y ∷ xs) (there .a y xs pf) with a == y
    equalFilter-fun a .(a ∷ xs) (there .a .a xs pf) | yes refl = there a a (filter (isYes ∘ (_==_ a)) xs) (equalFilter-fun a xs pf)
    equalFilter-fun a .(y ∷ xs) (there .a y xs pf) | no p = equalFilter-fun a xs pf
    
    {-
    equalFilter-inj-helper : ∀{l} {A : Set l} {{_ : Eq A}}
                           → (a x : A) (xs : List A)
                           → Injective (equalFilter-fun a xs)
    equalFilter-inj-helper  = ?
    
    equalFilter-fun-red : ∀{l} {A : Set l} {{_ : Eq A}}
                        → (a x : A) (xs : List A)
                        → (p q : a ∈ xs)
                        → equalFilter-fun a (x ∷ xs) (there a x xs p) ≡ equalFilter-fun a (x ∷ xs) (there a x xs q)
                        → equalFilter-fun a xs p ≡ equalFilter-fun a xs q
    equalFilter-fun-red a x xs p q pe with a == x
    equalFilter-fun-red a .a xs p q pe | yes refl = {!!}
    equalFilter-fun-red a x xs p q pe | no pr = {!!}
    
    
    equalFilter-inj : ∀{l} {A : Set l} {{_ : Eq A}}
                    → (a : A) (xs : List A)
                    → Injective (equalFilter-fun a xs)
    equalFilter-inj a .(a ∷ xs) (here .a xs) (here .a .xs) pe = refl
    equalFilter-inj a .(a ∷ xs) (here .a xs) (there .a .a .xs q) pe = {!!}
    equalFilter-inj a .(a ∷ xs) (there .a .a xs p) (here .a .xs) pe = {!!}
    equalFilter-inj a .(y ∷ xs) (there .a y xs p) (there .a .y .xs q) = {!!}
    -}
    
    equalFilter-inv : ∀(a : A) (xs : List A)
                    → a ∈ filter (isYes ∘ (_==_ a)) xs → a ∈ xs
    equalFilter-inv a [] ()
    equalFilter-inv a (x ∷ xs) p with a == x
    equalFilter-inv a (.a ∷ xs) (here .a ._) | yes refl = here a xs
    equalFilter-inv a (.a ∷ xs) (there .a .a ._ p) | yes refl = there a a xs (equalFilter-inv a xs p)
    equalFilter-inv a (x ∷ xs) p | no pne = there a x xs (equalFilter-inv a xs p) 
    
    {-
    equalFilter-inv-sec : ∀{l} {A : Set l} {{_ : Eq A}}
                        → (a : A) (xs : List A)
                        → Section equalFilter-inv a xs of equalFilter-fun a xs
    equalFilter-inv-sec a [] ()
    equalFilter-inv-sec a (x ∷ xs) p with a == x
    -}
    
    postulate
      equalFilter-sec : ∀(a : A) (xs : List A)
                      → Section equalFilter-fun a xs of equalFilter-inv a xs
      equalFilter-ret : ∀(a : A) (xs : List A)
                      → Retraction equalFilter-fun a xs of equalFilter-inv a xs
    
    equalFilter-lem : ∀(a : A) (xs : List A)
                    → a ∈ xs ↔ a ∈ filter (isYes ∘ (_==_ a)) xs
    equalFilter-lem a xs = equalFilter-fun a xs , equalFilter-inv a xs , equalFilter-sec a xs , equalFilter-ret a xs
  
    singleton-size : (a : A) → HasSize (a ∈ [ a ]) 1
    singleton-size a = size1-lem (a ∈ [ a ]) (here a []) λ { (here _ .[]) → refl ; (there _ _ .[] ()) }

    -- this would probably be a nice lemma to have
    -- remove-head : ∀(a : A) (xs : List A) (n : Nat) → HasSize (a ∈ a ∷ xs) (suc n) → HasSize (a ∈ xs) n
    -- remove-head a xs n sp = {!!}

    remove-head-1 : ∀(a : A) (xs : List A) → HasSize (a ∈ a ∷ xs) 1 → HasSize (a ∈ xs) 0
    remove-head-1 a [] s = size0-lem (a ∈ []) (λ ())
    remove-head-1 a (x ∷ xs) s = size0-lem (a ∈ x ∷ xs) lem
      where lem : a ∈ x ∷ xs → ⊥
            lem p with is-unique s (here a (x ∷ xs)) (there a a (x ∷ xs) p)
            lem p | ()

    reduce-empty-∈ : ∀{x xs} (a : A) → HasSize (a ∈ x ∷ xs) 0 → HasSize (a ∈ xs) 0
    reduce-empty-∈ {x} {xs} a s = size0-lem (a ∈ xs) λ p → is-empty s (there a x xs p)

    empty-elem : (a : A) (xs : List A) → (HasSize (a ∈ xs) 0) → [] ≡ filter (isYes ∘ (_==_ a)) xs
    empty-elem a [] s = refl
    empty-elem a (x ∷ xs) s with a == x
    ... | yes refl = ⊥-elim (is-empty s (here a xs))
    ... | no neq rewrite sym (empty-elem a xs (reduce-empty-∈ a s)) = refl

    singleton-elem : (a : A) (xs : List A) → (HasSize (a ∈ xs) 1) → [ a ] ≡ filter (isYes ∘ (_==_ a)) xs
    singleton-elem a [] (f , _) with f zero
    singleton-elem a [] (f , _) | ()
    singleton-elem a (x ∷ xs) s with a == x
    singleton-elem a (.a ∷ xs) s | yes refl = cong (_∷_ a) (empty-elem a xs (remove-head-1 a xs s))
    ... | no neq = singleton-elem a xs s′
      where v : a ∈ xs 
            v = neq-there a x neq xs (get-unique s) 
            u : (a′ : a ∈ xs) → a′ ≡ v
            u a′ = there-Inj (is-unique s (there a x xs a′) (there a x xs v))
            s′ : HasSize (a ∈ xs) 1
            s′ = size1-lem (a ∈ xs) v u

