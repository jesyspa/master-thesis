open import Probability.Class using (Probability)
module Utility.List.Arithmetic (Q : Set) {{PQ : Probability Q}} where

open import ThesisPrelude
open import Algebra.MonoidHelpers
open import Algebra.Function
open import Algebra.SemiringProps Q
open import Probability.Class
open import Probability.PropsClass Q
open import Utility.List.Lookup
open import Utility.List.Props

module _ {{PPQ : ProbabilityProps}} where
  open ProbabilityProps PPQ
  open Probability PQ
  open import Algebra.Monoid Q 
  open SemiringProps srprops
  open CommMonoidProps +-is-comm-monoid
  open MonoidProps forget-comm
  sum-lem : (q p : Q) (xs : List Q)
          → q + foldl! _+_ p xs ≡ foldl! _+_ (p + q) xs
  sum-lem q p [] = op-comm q p
  sum-lem q p (x ∷ xs) =
    q + force (p + x) (λ z → foldl! _+_ z xs) 
      ≡⟨ cong (_+_ q) (forceLemma (p + x) λ z → foldl! _+_ z xs) ⟩
    q + foldl! _+_ (p + x) xs
      ≡⟨ cong (_+_ q) (sum-lem x p xs) ⟩ʳ
    q + (x + foldl! _+_ p xs)
      ≡⟨ op-assoc q x (foldl! _+_ p xs) ⟩
    (q + x) + foldl! _+_ p xs
      ≡⟨ sum-lem (q + x) p xs ⟩
    foldl! _+_ (p + (q + x)) xs 
      ≡⟨ cong (λ e → foldl! _+_ e xs) (op-assoc p q x) ⟩
    foldl! _+_ (p + q + x) xs 
      ≡⟨ forceLemma (p + q + x) (λ z → foldl! _+_ z xs) ⟩ʳ
    force (p + q + x) (λ z → foldl! _+_ z xs)
    ∎

  sum-rewrite-gen : (q p : Q) (xs : List Q)
                  → q + foldl! _+_ p xs ≡ foldl! _+_ p (q ∷ xs)
  sum-rewrite-gen q p [] = op-comm q p ⟨≡⟩ʳ forceLemma (p + q) id
  sum-rewrite-gen q p (x ∷ xs) =
    q + force (p + x) (λ z′ → foldl! _+_ z′ xs)
      ≡⟨ cong (_+_ q) (forceLemma (p + x) (λ z′ → foldl! _+_ z′ xs))  ⟩
    q + foldl! _+_ (p + x) xs
      ≡⟨ cong (_+_ q) (sum-lem x p xs) ⟩ʳ
    q + (x + foldl! _+_ p xs)
      ≡⟨ op-assoc q x (foldl! _+_ p xs) ⟩
    q + x + foldl! _+_ p xs
      ≡⟨ cong (λ e → e + foldl! _+_ p xs) (op-comm q x) ⟩
    x + q + foldl! _+_ p xs
      ≡⟨ op-assoc x q (foldl! _+_ p xs) ⟩ʳ
    x + (q + foldl! _+_ p xs)
      ≡⟨ cong (_+_ x) (sum-lem q p xs) ⟩
    x + foldl! _+_ (p + q) xs
      ≡⟨ sum-rewrite-gen x (p + q) xs ⟩
    foldl! _+_ (p + q) (x ∷ xs)
      ≡⟨ forceLemma (p + q) (λ z′ → foldl! _+_ z′ (x ∷ xs)) ⟩ʳ
    force (p + q) (λ z′ → foldl! _+_ z′ (x ∷ xs))
    ∎

  sum-rewrite : (x : Q) (xs : List Q)
              → x + sum xs ≡ sum (x ∷ xs)
  sum-rewrite x xs = sum-rewrite-gen x zro xs

  singleton-sum-id : Retraction sum {A = Q} of [_]
  singleton-sum-id x =
    x
      ≡⟨ +-unit-left x ⟩
    zro + x
      ≡⟨ forceLemma (zro + x) id ⟩ʳ
    force (zro + x) id
    ∎

  sum-append-dist-gen : (xs ys : List Q) (q : Q)
                      → foldl! _+_ q (xs ++ ys) ≡ foldl! _+_ q xs + sum ys
  sum-append-dist-gen [] ys q = cong (λ e → foldl! _+_ e ys) (+-unit-left q) ⟨≡⟩ʳ sum-lem q zro ys
  sum-append-dist-gen (x ∷ xs) ys q =
    foldl! _+_ q (x ∷ xs ++ ys)
      ≡⟨ sum-rewrite-gen x q (xs ++ ys) ⟩ʳ
    x + foldl! _+_ q (xs ++ ys)
      ≡⟨ cong (_+_ x) (sum-append-dist-gen xs ys q)  ⟩
    x + (foldl! _+_ q xs + sum ys)
      ≡⟨ op-assoc x (foldl! _+_ q xs) (sum ys) ⟩
    x + foldl! _+_ q xs + sum ys
      ≡⟨ cong (λ e → e + sum ys) (sum-rewrite-gen x q xs) ⟩
    foldl! _+_ q (x ∷ xs) + sum ys
    ∎

  sum-append-dist : (xs ys : List Q)
                  → sum (xs ++ ys) ≡ sum xs + sum ys
  sum-append-dist xs ys = sum-append-dist-gen xs ys zro

  concat-sum-swap : (xss : List (List Q))
                  → sum (concat xss) ≡ sum (map sum xss)
  concat-sum-swap [] = refl
  concat-sum-swap (xs ∷ xss) =
    sum (xs ++ concat xss)
      ≡⟨ sum-append-dist xs (concat xss) ⟩
    sum xs + sum (concat xss)
      ≡⟨ cong (_+_ (sum xs)) (concat-sum-swap xss ) ⟩
    sum xs + sum (map sum xss)
      ≡⟨ sum-rewrite (sum xs) (map sum xss) ⟩
    sum (sum xs ∷ map sum xss)
    ∎

  module _ {A : Set} {{_ : Eq A}} where
    combine-sum-concat : (xs : List (SearchList A Q))
                       → (a : A)
                       → combine-vals sum a (concat xs) ≡ sum (map (combine-vals sum a) xs)
    combine-sum-concat xs a =
      sum (filter-vals a (concat xs))
        ≡⟨ cong sum (filter-vals-concat xs a ) ⟩
      sum (concat (map (filter-vals a) xs)) 
        ≡⟨ concat-sum-swap (map (filter-vals a) xs) ⟩
      sum (map sum (map (filter-vals a) xs)) 
        ≡⟨ cong sum (map-comp sum (filter-vals a) xs) ⟩ʳ
      sum (map (sum ∘′ filter-vals a) xs) 
      ∎

  sum-replicate : (n : Nat) (q : Q)
                → embed n * q ≡ sum (replicate n q)
  sum-replicate zero q rewrite sym embed-zero = sym (zro-left-nil q)
  sum-replicate (suc n) q rewrite sym (embed-succ n) =
    (one + embed n) * q
      ≡⟨ +*-right-dist one (embed n) q ⟩
    one * q + embed n * q
      ≡⟨ cong (λ e → e + embed n * q) (*-unit-left q) ⟩ʳ
    q + embed n * q
      ≡⟨ cong (_+_ q) (sum-replicate n q) ⟩
    q + sum (replicate n q)
      ≡⟨ sum-rewrite q (replicate n q) ⟩
    sum (q ∷ replicate n q)
    ∎

  mul-sum : (q : Q) (xs : List Q)
          → q * sum xs ≡ sum (map (_*_ q) xs)
  mul-sum q [] = sym (zro-right-nil q) 
  mul-sum q (x ∷ xs) =
    q * sum (x ∷ xs)
      ≡⟨ (cong (_*_ q) $ sum-rewrite x xs) ⟩ʳ
    q * (x + sum xs)
      ≡⟨ +*-left-dist q x (sum xs) ⟩
    q * x + q * sum xs
      ≡⟨ (cong (_+_ (q * x)) $ mul-sum q xs) ⟩
    q * x + sum (map (_*_ q) xs)
      ≡⟨ sum-rewrite (q * x) (map (_*_ q) xs) ⟩
    sum (q * x ∷ map (_*_ q) xs)
    ∎

{-
  sum-perm-invariant : PermInvariant {A = A} sum
  sum-perm-invariant [] φ = {!!}
  sum-perm-invariant (x ∷ xs) φ = {!!}
-}
