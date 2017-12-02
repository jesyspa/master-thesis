module LC where

open import MyPrelude
open import Elem

-- Based strongly on the paper Intrinsically Typed Definitional Interpreters
data Ty : Set where
  bool : Ty
  nat : Ty
  _⇒_ : Ty → Ty → Ty

Ctx : Set
Ctx = List Ty

data Expr (Γ : Ctx) : Ty → Set where
  bool : Bool → Expr Γ bool
  nat : Nat → Expr Γ nat
  var : ∀{t} → t ∈ Γ → Expr Γ t
  if : ∀{t} → Expr Γ bool → Expr Γ t → Expr Γ t → Expr Γ t
  lam : ∀{t u} → Expr (t ∷ Γ) u → Expr Γ (t ⇒ u)
  _·_ : ∀{t u} → Expr Γ (t ⇒ u) → Expr Γ t → Expr Γ u

mutual
  data Val : Ty → Set where
    nat : Nat → Val nat
    bool : Bool → Val bool
    ⟨_,_⟩ : ∀{Γ t u} → Expr (t ∷ Γ) u → Env Γ → Val (t ⇒ u)

  Env : Ctx → Set
  Env = All Val

M : Ctx → Set → Set
M Γ A = Env Γ → A

return : ∀{Γ A} → A → M Γ A
return a = const a

infixl 20 _>>=_
_>>=_ : ∀{Γ A B} → M Γ A → (A → M Γ B) → M Γ B
e >>= f = λ z → f (e z) z

{-# TERMINATING #-}
eval : ∀{Γ t} → Expr Γ t → M Γ (Val t)
eval (bool x) = return (bool x)
eval (nat x) = return (nat x)
eval (var x) = λ env → lookup env x 
eval (if c e₁ e₂) =  eval c >>= λ { (bool b) → if b then eval e₁ else eval e₂ }
eval (lam e) = λ env → ⟨ e , env ⟩
eval (e₁ · e₂) = eval e₁ >>= (λ { ⟨ body , env' ⟩ → eval e₂ >>= λ v _ → eval body (v ∷ env') }) 
