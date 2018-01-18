open import Probability.Class using (Probability)
module Distribution.List (Q : Set) {{PQ : Probability Q}} where

open import Distribution.List.Definition Q public
open import Distribution.List.BasicProps Q public
open import Distribution.List.MonadProps Q public
open import Distribution.List.DistProps Q public
