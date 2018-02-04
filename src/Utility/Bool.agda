module Utility.Bool where

open import ThesisPrelude
open import Algebra.Function

xor : Bool → Bool → Bool
xor x y = isNo (x == y)

xorʳ : Bool → Bool → Bool
xorʳ = flip xor

xor-self-inverse : (x y : Bool) → y ≡ xor x (xor x y)
xor-self-inverse false false = refl
xor-self-inverse false true = refl
xor-self-inverse true false = refl
xor-self-inverse true true = refl

xor-symmetric : (x y : Bool) → xor x y ≡ xorʳ x y
xor-symmetric false false = refl
xor-symmetric false true = refl
xor-symmetric true false = refl
xor-symmetric true true = refl

xorʳ-self-inverse : (x y : Bool) → y ≡ xorʳ x (xorʳ x y)
xorʳ-self-inverse x y rewrite sym (xor-symmetric x (xorʳ x y))
                            | sym (xor-symmetric x y)
                            = xor-self-inverse x y

xor-Bij : (x : Bool) → Bijective (xor x)
xor-Bij x = xor x , xor-self-inverse x , xor-self-inverse x 

nxor : Bool → Bool → Bool
nxor x y = isYes (x == y)

nxor-symmetric : (x y : Bool) → nxor x y ≡ nxor y x
nxor-symmetric false false = refl
nxor-symmetric false true = refl
nxor-symmetric true false = refl
nxor-symmetric true true = refl

nxor-self-inverse : (x y : Bool) → y ≡ nxor x (nxor x y)
nxor-self-inverse false false = refl
nxor-self-inverse false true = refl
nxor-self-inverse true false = refl
nxor-self-inverse true true = refl

nxor-Bij : (x : Bool) → Bijective (nxor x)
nxor-Bij x = nxor x , nxor-self-inverse x , nxor-self-inverse x 

if-dist : ∀{l}{A B : Set l}(b : Bool)(f : A → B)(a₀ a₁ : A)
        → f (if b then a₀ else a₁) ≡ (if b then f a₀ else f a₁) 
if-dist false f a₀ a₁ = refl
if-dist true f a₀ a₁ = refl

if-const-dist : ∀{l}{A : Set l}(b : Bool)(a : A)
              → a ≡ (if b then a else a)
if-const-dist false a = refl
if-const-dist true a = refl
    
