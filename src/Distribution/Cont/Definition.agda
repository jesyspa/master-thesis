open import Probability.Class using (Probability)
module Distribution.Cont.Definition (Q : Set) {{QC : Probability Q}} where

open Probability QC
open import ThesisPrelude
open import Distribution.Class
open import Probability.Class
open import Utility.Vector

ContDist : Set → Set
ContDist A = (A → Q) → Q

fmap-CD : ∀{A B} → (A → B) → ContDist A → ContDist B
fmap-CD f cd = λ p → cd (p ∘′ f)

instance
  FunctorContDist : Functor ContDist
  FunctorContDist = record { fmap = fmap-CD }

pure-CD : ∀{A} → A → ContDist A
pure-CD a = λ z → z a

ap-CD : ∀{A B} → ContDist (A → B) → ContDist A → ContDist B
ap-CD cf ca = λ p → ca λ a → cf λ g → p (g a)

instance
  ApplicativeContDist : Applicative ContDist
  ApplicativeContDist = record { pure = pure-CD ; _<*>_ = ap-CD }

bind-CD : ∀{A B} → ContDist A → (A → ContDist B) → ContDist B
bind-CD ca f = λ p → ca (λ z → f z p)
  
instance
  MonadContDist : Monad ContDist
  MonadContDist = record { _>>=_ = bind-CD }


uniform-CD : ∀ n → ContDist (BitVec n)
uniform-CD n = λ p → negpow2 n * sum (map p (all-bitvecs n)) 

sample : ∀{A}{{_ : Eq A}} → ContDist A → A → Q
sample ca a = ca λ a′ → if isYes (a == a′) then one else zro 

data _≡CD_ (A : Set){{_ : Eq A}} : 
{-
    uniform : ∀ n → D (BitVec n)
    sample : ∀{A} → {{_ : Eq A}} → D A → A → probability
    _≡D_ : ∀{A} → {{_ : Eq A}} → D A → D A → Set

-}
