module Utility.List.Elem.AppendProps {l} {A : Set l} where

open import ThesisPrelude
open import Algebra.Function
open import Utility.List.Elem.Definition
open import Utility.List.Elem.Append

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
