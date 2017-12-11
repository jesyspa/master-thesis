module AbstractProb where

open import MyPrelude

-- I want to figure out what kind of requirements I can/must place on
-- probabilities for them to be usable.

-- What we have, essentially, are fixed-point numbers with n bits before
-- the decimal point.  We denote this type by Fixed n.

-- Since I will only be working with postulates, I ignore the definitions
-- for now.

-- We want a preorder structure on Nat.
data _≤N_ : Nat → Nat → Set where
  zero-≤ : ∀{n} → zero ≤N n
  suc-≤ : ∀{n k} → n ≤N k → suc n ≤N suc k

abstract
  -- Type for fixed-point bitstrings.  n is the number of bits before the point.
  data Fixed (n : Nat) : Set where

  -- A proof that p can be reduced to a Fixed n.
  data Reducible {n k} (le : n ≤N k) : Fixed k → Set where

Prob : Set
Prob = Fixed zero

IsProb : ∀{k} → Fixed k → Set
IsProb p = Reducible zero-≤ p

postulate
  max : Nat → Nat → Nat
  left-≤max : ∀ n k → n ≤N max n k
  right-≤max : ∀ n k → k ≤N max n k

  -- We have some kind of injection from numbers with fewer bits into numbers
  -- with more bits.
  inj : ∀{n k} → n ≤N k → Fixed n → Fixed k
  
  -- Reducible numbers can be reduced.
  red : ∀{n k} → (le : n ≤N k) → (a : Fixed k)
      → Reducible le a
      → Fixed n 
  
  -- Any number that is the result of an injection is reducible.
  inj-reducible : ∀{n k} → (le : n ≤N k)
                → (a : Fixed n)
                → Reducible le (inj le a)
  
  -- Reduction is a retraction of injection.
  red-inj-rectraction : ∀{n k} → (le : n ≤N k)
                      → (a : Fixed n)
                      → a ≡ red le (inj le a) (inj-reducible le a)

  -- I suspect that any particular reduction should be unique, and thus reducibility
  -- should be proof-irrelevant.  Not 100% sure, though. 
  ≤N-pi : ∀{n k} → (p q : n ≤N k) → p ≡ q
  Reducible-pi : ∀{n k} → {le : n ≤N k}
               → (a : Fixed k)
               → (p q : Reducible le a)
               → p ≡ q
  
-- We want an easy way of being able to express that two values are equal (even when
-- they are in differently-represented types).
infix 4 _≡F_
data _≡F_ {n k : Nat} : Fixed n → Fixed k → Set where
  embed-≡F : {a : Fixed n} → {b : Fixed k}
           → inj (left-≤max n k) a ≡ inj (right-≤max n k) b
           → a ≡F b

postulate
  ≡F-pi : ∀{n k} → {a : Fixed n} → {b : Fixed k}
        → (p q : a ≡F b)
        → p ≡ q

  -- Properties like this should make it easier to prove that what we're working
  -- with is still small.  I'm not sure, though.
  -- This is an (annoying) departure from the usual pattern of x ≡ e(x), but I can't
  -- preserve both that and the n ≤ k pattern.  Dunno which one is more important.
  ≡F⇒inj : ∀{n k} → (le : n ≤N k) → (a : Fixed n) → (b : Fixed k)
         → a ≡F b
         → inj le a ≡ b 
  
infixr 6 _+F_
postulate
  -- Bitsize required to store the result of an addition.
  -- This operations is almost certainly *not* associative.
  -- It should in practice be commutative, but I'm not sure I want to assume that.
  add-bs : Nat → Nat → Nat
  
  -- Addition operation
  _+F_ : ∀{n k} → Fixed n → Fixed k → Fixed (add-bs n k)

  -- On the object level, these should be true.
  +F-comm : ∀{n k} → (a : Fixed n) → (b : Fixed k)
          → a +F b ≡F b +F a
  +F-assoc : ∀{n k l} → (a : Fixed n) → (b : Fixed k) → (c : Fixed l)
           → a +F (b +F c) ≡F (a +F b) +F c

-- We first introduce an ordering relation within a specific fixed point offset and then
-- generalise that to an ordering relation on all fixed-point numbers.
infix 4 _≤FR_ _≤F_
abstract
  data _≤FR_ {n} : Fixed n → Fixed n → Set where

data _≤F_ {n k} : Fixed n → Fixed k → Set where
  embed-≤F : {a : Fixed n} → {b : Fixed k}
           → inj (left-≤max n k) a ≤FR inj (right-≤max n k) b
           → a ≤F b

  
infixr 7 _*F_
postulate
  -- Bit size necessary to store result of multiplication.
  mul-bs : Nat → Nat → Nat
  mul-bs-zero-left-identity : ∀ n → zero ≡ mul-bs zero n
  mul-bs-zero-right-identity : ∀ n → zero ≡ mul-bs n zero

  -- Multiplication operation
  _*F_ : ∀{n k} → Fixed n → Fixed k → Fixed (mul-bs n k)

  
  -- On the object level, these should be true.
  *F-comm : ∀{n k} → (a : Fixed n) → (b : Fixed k)
          → a *F b ≡F b *F a
  *F-assoc : ∀{n k l} → (a : Fixed n) → (b : Fixed k) → (c : Fixed l)
           → a *F (b *F c) ≡F (a *F b) *F c
  *F-+F-dist : ∀{n k l} → (a : Fixed n) → (b : Fixed k) → (c : Fixed l)
             → a *F (b +F c) ≡F a *F b +F a *F c


postulate
  -- Some useful constants and their properties.
  0F : Fixed zero
  1F : Fixed zero
  2^_F : ∀ n → Fixed n

  0F-bot : (a : Fixed zero) → 0F ≤FR a
  1F-top-at-0 : (a : Fixed zero) → a ≤FR 1F 
  2^F-top : ∀{n} → (a : Fixed n) → a ≤FR 2^ n F

  0F-+F-left-identity : ∀{n} → (a : Fixed n)
                      → a ≡F 0F +F a
  0F-+F-right-identity : ∀{n} → (a : Fixed n)
                       → a ≡F a +F 0F 
  1F-*F-left-identity : ∀{n} → (a : Fixed n)
                      → a ≡F 1F *F a
  1F-*F-right-identity : ∀{n} → (a : Fixed n)
                       → a ≡F a *F 1F
  0F-*F-left-nil : ∀{n} → (a : Fixed n)
                 → 0F ≡F 0F *F a
  0F-*F-right-nil : ∀{n} → (a : Fixed n)
                 → 0F ≡F a *F 0F 

-- Since we are working with lists of unknown size, we need to also be able to perform all these
-- operations on existentially quantified Fixeds.
XFixed : Set
XFixed = Σ Nat Fixed

toXFixed : ∀{n} → Fixed n → XFixed
toXFixed {n} a = n , a

infixr 6 _+XF_
infixr 7 _*XF_
postulate
  _+XF_ : XFixed → XFixed → XFixed
  +XF-comm : (a b : XFixed)
           → a +XF b ≡ b +XF a
  +XF-assoc : (a b c : XFixed)
            → a +XF (b +XF c) ≡ (a +XF b) +XF c

  _*XF_ : XFixed → XFixed → XFixed 
  *XF-comm : (a b : XFixed)
           → a *XF b ≡ b *XF a
  *XF-assoc : (a b c : XFixed)
            → a *XF (b *XF c) ≡ (a *XF b) *XF c
  *XF-+XF-dist : (a b c : XFixed)
               → a *XF (b +XF c) ≡ a *XF b +XF a *XF c


infix 4 _≤XF_
data _≤XF_ : XFixed → XFixed → Set where
  embed-≤XF : ∀{n k} → {a : Fixed n} → {b : Fixed k}
            → a ≤F b
            → toXFixed a ≤XF toXFixed b

postulate
  0XF : XFixed
  1XF : XFixed
  2^_XF : Nat → XFixed

  0XF-+XF-left-identity  : (a : XFixed) → a   ≡ 0XF +XF a
  0XF-+XF-right-identity : (a : XFixed) → a   ≡ a   +XF 0XF
  1XF-*XF-left-identity  : (a : XFixed) → a   ≡ 1XF *XF a
  1XF-*XF-right-identity : (a : XFixed) → a   ≡ a   *XF 1XF 
  0XF-*XF-left-nil       : (a : XFixed) → 0XF ≡ 0XF *XF a
  0XF-*XF-right-nil      : (a : XFixed) → 0XF ≡ a   *XF 0XF

-- This isn't proof-irrelevant; that's a bit of a bummer.
-- I should define a < relation (or use Ulf's LessNat) and rephrase it that way.
-- It's kind of nasty to have both < and ≤ here, though. :/
-- Maybe a < b = a ≤ b × (¬ a ≡ b)?
data XConvertible : Nat → XFixed → Set where
  x-identity : ∀{n} → (a : Fixed n) → XConvertible n (n , a)
  x-injectable : ∀{n k} → (le : n ≤N k) → (a : Fixed n) → XConvertible k (n , a)
  x-reducible : ∀{n k} → (le : n ≤N k) → (a : Fixed k)
              → Reducible le a
              → XConvertible n (k , a) 

XIsProb : XFixed → Set
XIsProb = XConvertible zero 

-- I need some lemmas to prove things are probabilities.
