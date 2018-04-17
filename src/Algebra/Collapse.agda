open import ThesisPrelude
module Algebra.Collapse {l}(A : Set l) where

Collapse : {{_ : Dec A}} → Set
Collapse {{yes _}} = ⊤
Collapse {{no  _}} = ⊥

Collapse-match : ∀{l′}{B : Set l′}{{_ : Dec A}} → (A → B) → Collapse → B
Collapse-match {{yes a}} f tt = f a
Collapse-match {{no  _}} f ()

Collapse-prop : {{_ : Dec A}}(x y : Collapse) → x ≡ y
Collapse-prop {{yes _}} tt tt = refl
Collapse-prop {{no _}} () ()
