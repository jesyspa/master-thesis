module SLC where

open import MyPrelude
open import Elem
open import ListDist

-- Based strongly on the paper Intrinsically Typed Definitional Interpreters
data Ty : Set where
  bool : Ty
  nat : Ty
  _⇒_ : Ty → Ty → Ty

Ctx : Set
Ctx = List Ty

data Expr (Γ : Ctx) : Ty → Set where
  bool : Bool                                   → Expr Γ bool
  nat : Nat                                     → Expr Γ nat
  var : ∀{t} → t ∈ Γ                            → Expr Γ t
  if : ∀{t} → Expr Γ bool → Expr Γ t → Expr Γ t → Expr Γ t
  lam : ∀{t u} → Expr (t ∷ Γ) u                 → Expr Γ (t ⇒ u)
  _·_ : ∀{t u} → Expr Γ (t ⇒ u) → Expr Γ t      → Expr Γ u
  choice : Expr Γ nat                           → Expr Γ nat
  eq : Expr Γ nat → Expr Γ nat                  → Expr Γ bool

mutual
  MVal : (Set → Set) → Ty → Set
  MVal m bool = Bool
  MVal m nat = Nat
  MVal m (t ⇒ s) = MVal m t → m (MVal m s)

  Env : (Set → Set) → Ctx → Set
  Env m = All (MVal m)

eval : ∀{Γ t} → Env Dist Γ → Expr Γ t → Dist (MVal Dist t)
eval env (bool x)     = return x 
eval env (nat x)      = return x
eval env (var x)      = return (lookup env x)
eval env (if c e₁ e₂) = eval env c >>= λ b → if b then eval env e₁ else eval env e₂ 
eval env (lam e)      = return λ t → eval (t ∷ env) e 
eval env (e₁ · e₂)    = eval env e₁ >>= λ ve₁ → eval env e₂ >>= ve₁
eval env (choice e)   = eval env e >>= \n → uniform n >>= λ x → return (finToNat x)
eval env (eq e₁ e₂)   = eval env e₁ >>= λ ve₁ → eval env e₂ >>= λ ve₂ → return (isYes (ve₁ == ve₂)) 

test : Expr [] (nat ⇒ (nat ⇒ nat))
test = lam $ lam $ if (eq (choice (nat 2)) (nat 0)) (var here) (var (there here))

infixl 20 _<m>_
_<m>_ : ∀{A B} → Dist (A → Dist B) → Dist A → Dist B
f <m> a = f >>= \vf → a >>= vf 

test' : Nat → Nat → Dist Nat
test' a b = eval [] test <m> return a <m> return b