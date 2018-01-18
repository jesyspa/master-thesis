open import Probability.Class using (Probability)
module Distribution.List.MonadProps (Q : Set) {{PQ : Probability Q}} where

open import ThesisPrelude
open import Distribution.List.Definition Q
open import Algebra.Monoid Q
open import Probability.Class
open import Algebra.SemiringProps Q
open import Probability.PropsClass Q
open import Utility.List
open import Utility.Writer Q

open Probability PQ

module _ {{PPQ : ProbabilityProps}} where
  open ProbabilityProps PPQ
  open SemiringProps srprops
  instance
    private
      MonoidPropsMulQ : MonoidProps
      MonoidPropsMulQ = *-is-monoid
  
  import Utility.Writer.Transformer Q List as WriterT
  open import Algebra.MonadProps ListDist
  instance
    MonadPropsListDist : MonadProps
    MonadPropsListDist = WriterT.Props.writer-monad-props-composition
