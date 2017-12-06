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

weaken-bound : ∀{n p} → PPDepthBound n p → PPDepthBound (suc n) p
weaken-bound end-depth = end-depth
weaken-bound (up-step db) = up-step (weaken-bound db)
weaken-bound (down-step db) = down-step (weaken-bound db)

-- repr {n} p = 2^(n+1) * [p]
repr : ∀{n} → (p : ProbPath) → (PPDepthBound n p) → Nat
repr (down p) (down-step x) = repr p x
repr (up p) (up-step {n} x) = pow2 (suc n) +N repr p x
repr {n} halfway _ = pow2 n

repr-lem : ∀{n p} → {db : PPDepthBound n p} → repr {suc n} p (weaken-bound db) ≡ 2 *N repr {n} p db
repr-lem {db = end-depth} = refl
repr-lem {.(suc n)} {up p} {db = up-step {n} db} =
  repr {suc (suc n)} (up p) (up-step (weaken-bound db))
    ≡⟨ refl ⟩
  pow2 (suc (suc n)) +N repr p (weaken-bound db)
    ≡⟨ cong (λ x → pow2 (suc (suc n)) +N x) (repr-lem {db = db}) ⟩
  pow2 (suc (suc n)) +N 2 *N repr {n} p db
    ≡⟨ refl ⟩ 
  2 *N pow2 (suc n) +N 2 *N repr {n} p db
    ≡⟨ nat-dist-lem 2 (pow2 (suc n)) (repr p db) ⟩
  2 *N (pow2 (suc n) +N repr {n} p db)
    ≡⟨ refl ⟩
  2 *N repr {suc n} (up p) (up-step db)
  ∎
repr-lem {n} {down p} {db = down-step db} = 
  repr {suc n} (down p) (down-step (weaken-bound db))
    ≡⟨ refl ⟩
  repr p (weaken-bound db)
    ≡⟨ repr-lem {db = db} ⟩
  2 *N repr p db
    ≡⟨ refl ⟩
  2 *N repr (down p) (down-step db)
  ∎

PPDepthBound-pi : ∀{n} → (p : ProbPath) → (ppa ppb : PPDepthBound n p) → ppa ≡ ppb
PPDepthBound-pi (down p) (down-step ppa) (down-step ppb) = cong down-step (PPDepthBound-pi p ppa ppb)
PPDepthBound-pi (up p) (up-step ppa) (up-step ppb) = cong up-step (PPDepthBound-pi p ppa ppb)
PPDepthBound-pi halfway end-depth end-depth = refl

postulate
  repr-avg-lem : ∀{p q n}
               → (pp : PPDepthBound n p) → (pq : PPDepthBound n q) → (ppq : PPDepthBound n (PP-avg p q))
               → repr {n} p pp +N repr {n} q pq ≡ 2 *N repr {n} (PP-avg p q) ppq

  repr-mul-lem : ∀{p q n}
               → (pp : PPDepthBound n p) → (pq : PPDepthBound n q) → (ppq : PPDepthBound n (PP-mul p q))
               → repr {n} p pp *N repr {n} q pq ≡ repr {n} (PP-mul p q) ppq

  repr-uni-prop : ∀{p q}
                → ((n : Nat) → (pp : PPDepthBound n p) → (pq : PPDepthBound n q) → repr {n} p pp ≡ repr {n} q pq)
                → p ≡ q

