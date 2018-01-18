import ThesisPrelude as TP
module Utility.List.Lookup.ElemProps {l}{A B : Set l}{{_ : TP.Eq A}} where

open import ThesisPrelude
open import Algebra.Function
open import Utility.List.Elem
open import Utility.List.Props
open import Utility.List.Lookup.Definition
open import Utility.List.Lookup.Elem

Index-to-∈-Inj : ∀(a : A) (xs : SearchList A B)
               → Injective (Index-to-∈ a xs)
Index-to-∈-Inj a [] {()} {()} eq
Index-to-∈-Inj a (.(a , b) ∷ xs) {here .a b .xs} {here .a .b .xs} eq = refl
Index-to-∈-Inj a (.(a , b) ∷ xs) {here .a b .xs} {there .a .(a , b) .xs q} ()
Index-to-∈-Inj a (.(a , b) ∷ xs) {there .a .(a , b) .xs p} {here .a b .xs} ()
Index-to-∈-Inj a (x ∷ xs) {there .a .x .xs p} {there .a .x .xs q} eq
  rewrite Index-to-∈-Inj a xs (there-Inj eq) = refl

∈-to-Index-Ret : ∀(a : A) (xs : SearchList A B)
               → Retraction ∈-to-Index a xs of Index-to-∈ a xs
∈-to-Index-Ret a .((a , b) ∷ xs) (here .a b xs) = refl
∈-to-Index-Ret a .(x ∷ xs) (there .a x xs p)
  rewrite sym (∈-to-Index-Ret a xs p) = refl

Index-to-∈-Ret : ∀(a : A) (xs : SearchList A B)
               → Retraction Index-to-∈ a xs of ∈-to-Index a xs
Index-to-∈-Ret a [] ()
Index-to-∈-Ret ._ ((a , b) ∷ xs) (here ._ ._) = refl
Index-to-∈-Ret a ((a′ , b) ∷ xs) (there .a ._ .(map fst xs) p)
    rewrite sym (Index-to-∈-Ret a xs p) = refl

∈-to-Index-Inj : ∀(a : A) (xs : SearchList A B)
               → Injective (∈-to-Index a xs)
∈-to-Index-Inj a [] {()} {()} eq
∈-to-Index-Inj ._ (_ ∷ _) {here ._ ._} {here ._ ._} refl = refl
∈-to-Index-Inj ._ ((a′ , b) ∷ xs) {here ._ ._} {there ._ ._ ._ _} ()
∈-to-Index-Inj ._ ((a′ , b) ∷ xs) {there ._ ._ ._ _} {here ._ ._} ()
∈-to-Index-Inj a ((a′ , b) ∷ xs) {there .a ._ ._ _} {there .a ._ ._ _} eq
    rewrite sym (∈-to-Index-Inj a xs (Index-there-Inj eq)) = refl
