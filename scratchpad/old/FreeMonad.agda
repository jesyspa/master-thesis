module FreeMonad where

record TS : Set₁ where
  field
    C : Set
    R : C → Set
open TS

data Free (ts : TS) (a : Set) : Set where
  Stop : a → Free ts a
  Step : (c : C ts) → ((r : R ts c) → Free ts a) → Free ts a

return : ∀{ts a} → a → Free ts a
return = Stop

_>>=_ : ∀{ts a b} → Free ts a → (a → Free ts b) → Free ts b
Stop x >>= f = f x
Step c x >>= f = Step c (λ r → x r >>= f)

