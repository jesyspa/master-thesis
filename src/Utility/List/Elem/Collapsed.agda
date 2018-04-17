open import ThesisPrelude
module Utility.List.Elem.Collapsed {l}{A : Set l}{{_ : Eq A}} where

open import Algebra.Collapse
open import Utility.List.Elem.Definition
open import Utility.List.Elem.Decidable

CElem : List A → Set l
CElem xs = Σ A λ a → Collapse (a ∈ xs) {{decide-elem a xs}}
