import ThesisPrelude as TP
module Utility.List.Lookup.Decidable {l}{A B : Set l}{{_ : TP.Eq A}} where

open import ThesisPrelude
open import Algebra.Function
open import Utility.List.Props
open import Utility.List.Elem
open import Utility.List.Lookup.Definition
open import Utility.List.Lookup.Elem

decide-Index : (a : A) (xs : SearchList A B)
             → Dec (Index a xs)
decide-Index a xs with decide-elem a (map fst xs)
... | yes p = yes (∈-to-Index a xs p)
... | no np = no (np ∘ Index-to-∈ a xs)
