module Utility.List.ElemProps where

open import ThesisPrelude
open import Utility.List.Props
open import Utility.List.Elem
open import Utility.List.Functions
open import Algebra.Equality
open import Algebra.Function
open import Algebra.ExactSize

module _ {l} {A : Set l} where
  there-Inj : ∀{x y : A} {xs : List A}
            → Injective (there x y xs)
  there-Inj refl = refl
  
  in-++-left-Inj : ∀{a : A} (xs ys : List A)
                 → Injective (in-++-left {a = a} xs ys)
  in-++-left-Inj [] ys {()}
  in-++-left-Inj (a ∷ xs) ys {here .a .xs} {here .a .xs} pe = refl
  in-++-left-Inj (a ∷ xs) ys {here .a .xs} {there .a .a .xs pb} ()
  in-++-left-Inj (a ∷ xs) ys {there .a .a .xs pa} {here .a .xs} ()
  in-++-left-Inj (x ∷ xs) ys {there a .x .xs pa} {there .a .x .xs pb} pe
    rewrite in-++-left-Inj xs ys (there-Inj pe) = refl
  
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
  
  module _ {B : Set l} where
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

    decide-elem : (a : A) (xs : List A) → Dec (a ∈ xs)
    decide-elem a [] = no λ ()
    decide-elem a (x ∷ xs) with a == x
    ... | yes refl = yes (here a xs)
    ... | no neq with decide-elem a xs
    ... | yes p = yes (there a x xs p)
    ... | no np = no f
      where f : ¬ (a ∈ x ∷ xs)
            f (here _ _) = neq refl
            f (there _ _ _ p) = np p

    filter-does-not-add-elements : (a : A) (xs : List A) (pd : A → Bool)
                                 → a ∈ filter pd xs → a ∈ xs
    filter-does-not-add-elements a [] pd ()
    filter-does-not-add-elements a (x ∷ xs) pd p with pd x
    filter-does-not-add-elements .x (x ∷ xs) pd (here .x ._)      | true = here x xs
    filter-does-not-add-elements a (x ∷ xs) pd (there .a .x ._ p) | true = there a x xs (filter-does-not-add-elements a xs pd p)
    ... | false = there a x xs (filter-does-not-add-elements a xs pd p)

    filter-does-not-add-elements-Inj : (a : A)(xs : List A)(pd : A → Bool)
                                     → Injective (filter-does-not-add-elements a xs pd)
    filter-does-not-add-elements-Inj a [] pd {()} {()} eq
    filter-does-not-add-elements-Inj a (x ∷ xs) pd {p} {q} eq with pd x
    filter-does-not-add-elements-Inj .x (x ∷ xs) pd {here .x ._} {here .x ._} eq | true = refl
    filter-does-not-add-elements-Inj .x (x ∷ xs) pd {here .x ._} {there .x .x ._ q} () | true
    filter-does-not-add-elements-Inj a (.a ∷ xs) pd {there .a .a ._ p} {here .a ._} () | true
    filter-does-not-add-elements-Inj a (x ∷ xs) pd {there .a .x ._ p} {there .a .x ._ q} eq | true
      = cong (there a x (filter pd xs)) (filter-does-not-add-elements-Inj a xs pd (there-Inj eq))
    ... | false = filter-does-not-add-elements-Inj a xs pd (there-Inj eq)
    
    filter-preserves-satisfying : (a : A) (xs : List A) (pd : A → Bool)
                                → IsTrue (pd a)
                                → a ∈ xs → a ∈ filter pd xs
    filter-preserves-satisfying a .(a ∷ xs) pd pf (here .a xs) with pd a
    ... | true = here a (filter pd xs)
    filter-preserves-satisfying a .(a ∷ xs) pd () (here .a xs) | false
    filter-preserves-satisfying a .(y ∷ xs) pd pf (there .a y xs p) with pd y
    ... | true = there a y (filter pd xs) (filter-preserves-satisfying a xs pd pf p)
    ... | false = filter-preserves-satisfying a xs pd pf p

    filter-preserves-Ret : (a : A)(xs : List A)(pd : A → Bool)(pf : IsTrue (pd a))
                         → Retraction filter-does-not-add-elements a xs pd of filter-preserves-satisfying a xs pd pf
    filter-preserves-Ret a .(a ∷ xs) pd pf (here .a xs) with pd a
    filter-preserves-Ret a .(a ∷ xs) pd () (here .a xs) | false
    filter-preserves-Ret a .(a ∷ xs) pd true (here .a xs) | true = refl
    filter-preserves-Ret a .(y ∷ xs) pd pf (there .a y xs p) with pd y
    filter-preserves-Ret a .(y ∷ xs) pd pf (there .a y xs p) | false = cong (there a y xs) $ filter-preserves-Ret a xs pd pf p
    filter-preserves-Ret a .(y ∷ xs) pd pf (there .a y xs p) | true = cong (there a y xs) $ filter-preserves-Ret a xs pd pf p

    filter-not-eq-preserves-elem : (a x : A) (xs : List A)
                                 → ¬ (x ≡ a) → a ∈ xs → a ∈ filter (isNo ∘ (_==_ x)) xs
    filter-not-eq-preserves-elem a x xs neq = filter-preserves-satisfying a xs (isNo ∘ (_==_ x)) (neq-is-no neq)

    unique-preserves-elem : (a : A) (xs : List A)
                          → a ∈ xs → a ∈ uniques xs
    unique-preserves-elem a ._ (here .a xs) = here a $ filter (isNo ∘ (_==_ a)) (uniques xs)
    unique-preserves-elem a ._ (there .a x xs p) with a == x
    ... | yes refl = here a (filter (isNo ∘ (_==_ a)) (uniques xs))
    ... | no neq = there a x (filter (isNo ∘ (_==_ x)) (uniques xs))
                             (filter-not-eq-preserves-elem a x (uniques xs) (neq ∘ sym)
                                                           (unique-preserves-elem a xs p))
                             
    filter-removes-unsatisfying : (a : A) (xs : List A) (pd : A → Bool)
                                → IsFalse (pd a)
                                → ¬ (a ∈ filter pd xs)
    filter-removes-unsatisfying a [] pd pf ()
    filter-removes-unsatisfying a (x ∷ xs) pd pf p with pd x | graphAt pd x
    filter-removes-unsatisfying .x (x ∷ xs) pd pf (here .x ._) | true | ingraph pig rewrite pig with pf
    ... | ()
    filter-removes-unsatisfying a (x ∷ xs) pd pf (there .a .x ._ p) | true | ingraph pig = filter-removes-unsatisfying a xs pd pf p
    filter-removes-unsatisfying a (x ∷ xs) pd pf p | false | ingraph pig = filter-removes-unsatisfying a xs pd pf p

{-
    postulate
      filter-uniques-functional : (a : A) (xs : List A) (f : List A → List A) (∀ x → fp : x ∈ xs → x ∈ f xs)
                                → (p : A → Bool)
                                → a ∈ filter p xs → a ∈ filter p (f xs)
-}
    filter-functional-inv : (a : A) (xs : List A) (f : List A → List A) (fp : a ∈ f xs → a ∈ xs)
                                  → (pd : A → Bool)
                                  → a ∈ filter pd (f xs) → a ∈ filter pd xs
    filter-functional-inv a xs f fp pd p with pd a | graphAt pd a
    ... | true | ingraph pig = filter-preserves-satisfying a xs pd (transport IsTrue (sym pig) it)
                                                           (fp (filter-does-not-add-elements a (f xs) pd p))
    ... | false | ingraph pig = ⊥-elim (filter-removes-unsatisfying a (f xs) pd (transport IsFalse (sym pig) it) p)

    not-in-filter-no : (a : A) (xs : List A)
                     → ¬ (a ∈ filter (isNo ∘ (_==_ a)) xs)
    not-in-filter-no a [] ()
    not-in-filter-no a (x ∷ xs) p with a == x
    ... | yes refl = not-in-filter-no a xs p
    not-in-filter-no a (.a ∷ xs) (here .a ._) | no neq = neq refl
    not-in-filter-no a (x ∷ xs) (there .a .x ._ p) | no neq = not-in-filter-no a xs p

    unique-preserves-elem-inv : (a : A) (xs : List A)
                              → a ∈ uniques xs → a ∈ xs
    unique-preserves-elem-inv a [] ()
    unique-preserves-elem-inv a (.a ∷ xs) (here .a ._) = here a xs
    unique-preserves-elem-inv a (x ∷ xs) (there .a .x ._ p) with x == a
    ... | yes refl = ⊥-elim (not-in-filter-no a xs (filter-functional-inv a xs uniques (unique-preserves-elem-inv a xs) (isNo ∘ (_==_ x)) p)) 
    ... | no neq = there a x xs (unique-preserves-elem-inv a xs (filter-does-not-add-elements a (uniques xs) (isNo ∘ (_==_ x)) p))

    if-not-a-then-nothing : (a : A) (xs : List A)
                          → ¬ (a ∈ filter (isYes ∘ (_==_ a)) xs) → [] ≡ filter (isYes ∘ (_==_ a)) xs
    if-not-a-then-nothing a [] np = refl
    if-not-a-then-nothing a (x ∷ xs) np with a == x
    ... | yes refl = ⊥-elim $ np (here a (filter (isYes ∘ (_==_ a)) xs)) 
    ... | no eq = if-not-a-then-nothing a xs np

    if-not-there-filter-empty : (a : A) (xs : List A)
                              → ¬ (a ∈ xs) → [] ≡ filter (isYes ∘ (_==_ a)) xs
    if-not-there-filter-empty a xs np = if-not-a-then-nothing a xs λ p → np (equalFilter-inv a xs p) 

    uniques-unique : (a : A) (xs : List A) (p : a ∈ xs)
                   → (q : a ∈ uniques xs) → q ≡ unique-preserves-elem a xs p
    uniques-unique a .(a ∷ xs) (here .a xs) (here .a ._) = refl
    uniques-unique a .(a ∷ xs) (here .a xs) (there .a .a ._ q)
      = ⊥-elim (not-in-filter-no a xs (filter-functional-inv a xs uniques (unique-preserves-elem-inv a xs) (isNo ∘ (_==_ a)) q))
    uniques-unique a .(a ∷ xs) (there .a .a xs p) (here .a ._) with a == a
    ... | yes refl = refl
    ... | no neq = ⊥-elim (neq refl)
    uniques-unique a .(x ∷ xs) (there .a x xs p) (there .a .x ._ q) with x == a | a == x
    ... | yes refl | yes refl = ⊥-elim $ not-in-filter-no a xs $ filter-functional-inv a xs uniques (unique-preserves-elem-inv a xs) (isNo ∘ (_==_ a)) q
    ... | no neq   | yes refl = ⊥-elim $ neq refl
    ... | yes refl | no neq   = ⊥-elim $ neq refl
    ... | no neq   | no neq′  = cong (there a x (filter (isNo ∘ (_==_ x)) (uniques xs))) lem
      where
        lem2 : filter-does-not-add-elements a (uniques xs) (isNo ∘ (_==_ x)) q
             ≡ unique-preserves-elem a xs p
        lem2 = uniques-unique a xs p (filter-does-not-add-elements a (uniques xs) (isNo ∘ (_==_ x)) q) 
        lem : q ≡ filter-not-eq-preserves-elem a x (uniques xs) (neq′ ∘ sym) (unique-preserves-elem a xs p)
        lem = filter-does-not-add-elements-Inj a (uniques xs) (isNo ∘ (_==_ x))
                (lem2 ⟨≡⟩ filter-preserves-Ret a (uniques xs) (isNo ∘ (_==_ x)) (neq-is-no (neq′ ∘ sym)) (unique-preserves-elem a xs p) ) 

    uniques-gives-singleton : (a : A) (xs : List A)
                            → a ∈ xs → [ a ] ≡ filter (isYes ∘ (_==_ a)) (uniques xs)
    uniques-gives-singleton a xs p = singleton-elem a (uniques xs) (size1-lem (a ∈ uniques xs) (unique-preserves-elem a xs p) (uniques-unique a xs p)) 
