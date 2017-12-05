module BitProbability where

open import MyPrelude

-- The semantics of this class are as follows:
-- [halfway] = 1/2
-- [down p] = 1/2 * [p]
-- [up p] = 1/2 (1 + [p])
data ProbTree : Set where
  down up : ProbTree → ProbTree
  halfway : ProbTree

data Prob : Set where
  never always : Prob
  sometimes : ProbTree → Prob

data _≤PT_ : ProbTree → ProbTree → Set where
  down≤halfway : ∀{p} → down p ≤PT halfway
  down≤up : ∀{p q} → down p ≤PT up q
  halfway≤up : ∀{p} → halfway ≤PT up p
  down-rec : ∀{p q} → p ≤PT q → down p ≤PT down q
  up : ∀{p q} → p ≤PT q → up p ≤PT up q

data _≤P_ : Prob → Prob → Set where
  never-bot : ∀{p} → never ≤P p
  always-top : ∀{p} → p ≤P always
  sometimes-lift : ∀{p q} → p ≤PT q → sometimes p ≤P sometimes q

to-end : (ProbTree → ProbTree) → ProbTree → ProbTree
to-end f (down x) = down (to-end f x)
to-end f (up x) = up (to-end f x) 
to-end f halfway = f halfway

-- The resulting ProbTree is rooted "one higher" than the two inputs, in order to detect overflow.
-- That is, 2*[p+q] = [p] + [q].
-- This allows us to detect overflow.
_+PT_ : ProbTree → ProbTree → ProbTree
halfway +PT halfway = halfway
halfway +PT up q    = up (down q)
halfway +PT down q  = down (up q)
up p +PT halfway    = up (down p)
down p +PT halfway  = down (up p)
down p +PT down q   = down (p +PT q)
down p +PT up q with p +PT q
...       | halfway = halfway
...       | up s    = up (down s)
...       | down s  = down (up s) 
up p +PT down q with p +PT q
...       | halfway = halfway
...       | up s    = up (down s)
...       | down s  = down (up s) 
up p +PT up q       = up (p +PT q)

test : up (up halfway) +PT down (down halfway) ≡ halfway
test = refl

-- Bounded addition
_+P_ : Prob → Prob → Prob
never +P q = q
always +P q = always
p +P never = p
p +P always = always
sometimes p +P sometimes q with p +PT q
... | down s = sometimes s
... | _ = always
  
