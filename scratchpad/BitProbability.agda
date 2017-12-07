module BitProbability where

open import MyPrelude
open import NatLemmas

-- The semantics of this class are as follows:
-- [halfway] = 1/2
-- [down p] = 1/2 * [p]
-- [up p] = 1/2 (1 + [p])
data ProbPath : Set where
  down up : ProbPath → ProbPath
  halfway : ProbPath

data Prob : Set where
  never always : Prob
  sometimes : ProbPath → Prob

data _≤PT_ : ProbPath → ProbPath → Set where
  down≤halfway : ∀{p} → down p ≤PT halfway
  down≤up : ∀{p q} → down p ≤PT up q
  halfway≤up : ∀{p} → halfway ≤PT up p
  down-rec : ∀{p q} → p ≤PT q → down p ≤PT down q
  up : ∀{p q} → p ≤PT q → up p ≤PT up q

data _≤P_ : Prob → Prob → Set where
  never-bot : ∀{p} → never ≤P p
  always-top : ∀{p} → p ≤P always
  sometimes-lift : ∀{p q} → p ≤PT q → sometimes p ≤P sometimes q

-- Computes the average of two probability paths.
PP-avg : ProbPath → ProbPath → ProbPath
PP-avg halfway  halfway    = halfway
PP-avg halfway  (up q)     = up (down q)
PP-avg halfway  (down q)   = down (up q)
PP-avg (up p)   halfway    = up (down p)
PP-avg (down p) halfway    = down (up p)
PP-avg (down p) (down q)   = down (PP-avg p q)
PP-avg (down p) (up q) with PP-avg p q
...              | halfway = halfway
...              | up s    = up (down s)
...              | down s  = down (up s) 
PP-avg (up p)   (down q) with PP-avg p q
...              | halfway = halfway
...              | up s    = up (down s)
...              | down s  = down (up s) 
PP-avg (up p) (up q)       = up (PP-avg p q)

PP-mul : ProbPath → ProbPath → ProbPath
PP-mul halfway q = down q
PP-mul p halfway = down p
PP-mul (down p) (down q) = down (down (PP-mul p q))
PP-mul (down p) (up q) = down (PP-avg p (PP-mul p q))
PP-mul (up p) (down q) = down (PP-avg q (PP-mul p q))
PP-mul (up p) (up q) = PP-avg (PP-avg p q) (up (PP-mul p q))

PP-neg : ProbPath → ProbPath
PP-neg (down p) = up (PP-neg p)
PP-neg (up p) = down (PP-neg p)
PP-neg halfway = halfway

P-neg : Prob → Prob
P-neg never = always
P-neg always = never
P-neg (sometimes p) = sometimes (PP-neg p)

P-avg : Prob → Prob → Prob
P-avg never never = never
P-avg never always = sometimes halfway
P-avg never (sometimes x) = sometimes (down x)
P-avg always never = sometimes halfway
P-avg always always = always
P-avg always (sometimes x) = sometimes (up x)
P-avg (sometimes x) never = sometimes (down x)
P-avg (sometimes x) always = sometimes (up x)
P-avg (sometimes p) (sometimes q) = sometimes (PP-avg p q)

infixl 6 _+P_
-- Bounded addition (min p+q, 1)
_+P_ : Prob → Prob → Prob
never +P q = q
always +P q = always
p +P never = p
p +P always = always
sometimes p +P sometimes q with PP-avg p q
... | down s = sometimes s
... | _ = always
  
infixl 7 _*P_
-- Multiplication (exact)
_*P_ : Prob → Prob → Prob
never *P q = never
always *P q = q
p *P never = never
p *P always = p
sometimes p *P sometimes q = sometimes (PP-mul p q)

infixl 7 _*NP_
-- Multiplication with a natural number
_*NP_ : Nat → Prob → Prob
zero *NP p = never
suc n *NP p = p +P (n *NP p)

data PPDepthBound : Nat → ProbPath → Set where
  end-depth : ∀{n} → PPDepthBound n halfway
  up-step : ∀{n p} → PPDepthBound n p → PPDepthBound (suc n) (up p)
  down-step : ∀{n p} → PPDepthBound n p → PPDepthBound (suc n) (down p)

data PDepthBound : Nat → Prob → Set where
  always-step : ∀{n} → PDepthBound (suc n) always
  never-step : ∀{n} → PDepthBound (suc n) never
  sometimes-step : ∀{n p} → PPDepthBound n p → PDepthBound (suc n) (sometimes p)

PP-weaken-bound : ∀{n p} → PPDepthBound n p → PPDepthBound (suc n) p
PP-weaken-bound end-depth = end-depth
PP-weaken-bound (up-step db) = up-step (PP-weaken-bound db)
PP-weaken-bound (down-step db) = down-step (PP-weaken-bound db)

P-weaken-bound : ∀{n p} → PDepthBound n p → PDepthBound (suc n) p
P-weaken-bound always-step = always-step
P-weaken-bound never-step = never-step 
P-weaken-bound (sometimes-step db) = sometimes-step (PP-weaken-bound db)

-- repr {n} p = 2^(n+1) * [p]
PP-repr : (n : Nat) → (p : ProbPath) → PPDepthBound n p → Nat
PP-repr (suc n) (down p) (down-step x) = PP-repr n p x
PP-repr (suc n) (up p) (up-step x) = pow2 (suc n) +N PP-repr n p x
PP-repr n halfway end-depth = pow2 n

PP-repr-halfway-lem : (n : Nat) → pow2 n ≡ PP-repr n halfway end-depth
PP-repr-halfway-lem zero = refl
PP-repr-halfway-lem (suc n) = refl 

PP-repr-lem : ∀{n p} → (db : PPDepthBound n p) → PP-repr (suc n) p (PP-weaken-bound db) ≡ 2 *N PP-repr n p db
PP-repr-lem {n} end-depth rewrite PP-repr-halfway-lem n = refl
PP-repr-lem (up-step db) rewrite PP-repr-lem db = auto 
PP-repr-lem (down-step db) rewrite PP-repr-lem db = auto 

PPDepthBound-pi : ∀{n} → (p : ProbPath) → (ppa ppb : PPDepthBound n p) → ppa ≡ ppb
PPDepthBound-pi (down p) (down-step ppa) (down-step ppb) = cong down-step (PPDepthBound-pi p ppa ppb)
PPDepthBound-pi (up p) (up-step ppa) (up-step ppb) = cong up-step (PPDepthBound-pi p ppa ppb)
PPDepthBound-pi halfway end-depth end-depth = refl

P-repr : (n : Nat) → (p : Prob) → PDepthBound n p → Nat
P-repr n .never never-step = 0 
P-repr n .always always-step = pow2 n
P-repr (suc n) (sometimes p) (sometimes-step db) = PP-repr n p db

postulate
  PP-repr-uni-prop : (p q : ProbPath)
                   → ((n : Nat) → (pp : PPDepthBound n p) → (pq : PPDepthBound n q) → PP-repr n p pp ≡ PP-repr n q pq)
                   → p ≡ q

  PP-repr-avg-lem : (p q : ProbPath) → (n : Nat) 
                  → (pp : PPDepthBound n p) → (pq : PPDepthBound n q) → (ppq : PPDepthBound n (PP-avg p q))
                  → PP-repr n p pp +N PP-repr n q pq ≡ 2 *N PP-repr n (PP-avg p q) ppq

  PP-repr-mul-lem : (p q : ProbPath) → (n : Nat) 
                  → (pp : PPDepthBound n p) → (pq : PPDepthBound n q) → (ppq : PPDepthBound n (PP-mul p q))
                  → PP-repr n p pp *N PP-repr n q pq ≡ PP-repr n (PP-mul p q) ppq

  P-repr-uni-prop : (p q : Prob)
                  → ((n : Nat) → (pp : PDepthBound n p) → (pq : PDepthBound n q) → P-repr n p pp ≡ P-repr n q pq)
                  → p ≡ q

  P-repr-plus-weak-lem : (p q : Prob) → (n : Nat) 
                 → (pp : PDepthBound n p) → (pq : PDepthBound n q) → (ppq : PDepthBound n (p +P q))
                 → LessNat (P-repr n p pp +N P-repr n q pq) (suc (P-repr n (p +P q) ppq))

  P-repr-plus-strong-lem : (p q : Prob) → (n : Nat) 
                 → (pp : PDepthBound n p) → (pq : PDepthBound n q) → (ppq : PDepthBound n (p +P q))
                 → P-avg p q ≤P sometimes halfway
                 → P-repr n p pp +N P-repr n q pq ≡ P-repr n (p +P q) ppq

  P-repr-mul-lem : (p q : Prob) → (n : Nat) 
                 → (pp : PDepthBound n p) → (pq : PDepthBound n q) → (ppq : PDepthBound n (p *P q))
                 → P-repr n p pp *N P-repr n q pq ≡ P-repr n (p *P q) ppq

  never-right-plus-unit-lem : (p : Prob) → p ≡ p +P never
  never-left-plus-unit-lem : (p : Prob) → p ≡ never +P p
  always-right-mul-unit-lem : (p : Prob) → p ≡ p *P always
  always-left-mul-unit-lem : (p : Prob) → p ≡ always *P p

  probpath-avg-comm : (p q : ProbPath) → PP-avg p q ≡ PP-avg q p
  probpath-mul-comm : (p q : ProbPath) → PP-mul p q ≡ PP-mul q p
  prob-add-comm : (p q : Prob) → p +P q ≡ q +P p
  prob-mul-comm : (p q : Prob) → p *P q ≡ q *P p

  probpath-mul-assoc : (p q r : ProbPath) → PP-mul (PP-mul p q) r ≡ PP-mul p (PP-mul q r)
  prob-plus-assoc : (p q r : Prob) → (p +P q) +P r ≡ p +P (q +P r)
  prob-mul-assoc : (p q r : Prob) → (p *P q) *P r ≡ p *P (q *P r)

  prob-nat-mul-dist : (n k : Nat) → (p : Prob) 
                    → n *NP p +P k *NP p ≡ (n +N k) *NP p

instance 
  ProbSemiring : Semiring Prob
  zro {{ProbSemiring}} = never
  one {{ProbSemiring}} = always
  _+_ {{ProbSemiring}} = _+P_
  _*_ {{ProbSemiring}} = _*P_
