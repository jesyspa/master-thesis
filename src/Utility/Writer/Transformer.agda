open import ThesisPrelude using (Monoid)
module Utility.Writer.Transformer {l} (Q : Set l) {{QM : Monoid Q}} where

open import ThesisPrelude
open import Algebra.Monoid
open import Utility.Writer.Writer Q
open import Utility.Writer.Props Q

-- Wait, I want the List monad transformer, not the Writer.  Never mind this.
