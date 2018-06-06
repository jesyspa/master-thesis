module Interaction.Indexed.UnsafeMemory where

open import ThesisPrelude
open import Algebra.Indexed.Monad
open import Algebra.Indexed.Atkey
open import Interaction.Indexed.InteractionStructure
open import Interaction.Indexed.FreeMonad
open import Interaction.Indexed.Implementation
open import Utility.BTAll

open IxMonad {{...}}

data MemCmd : Nat → Set where
  alloc-C   : ∀ s → MemCmd s
  dealloc-C : ∀ s → MemCmd (suc s)
  write-C   : ∀ s → (addr : Nat) → (val : Nat) → MemCmd s
  read-C    : ∀ s → (addr : Nat) → MemCmd s

data MemAllocResp : Set where
  alloc-success : MemAllocResp
  alloc-fail    : MemAllocResp

data MemReadResp : Set where
  read-success       : Nat → MemReadResp
  read-out-of-bounds :       MemReadResp

data MemWriteResp : Set where
  write-success       : MemWriteResp
  write-out-of-bounds : MemWriteResp

open InteractionStructure
Mem : IStruct (Leaf Nat)
Command   Mem (leaf  s) = MemCmd s
Response  Mem {leaf ._} (alloc-C s)   = MemAllocResp
Response  Mem {leaf ._} (dealloc-C s) = ⊤
Response  Mem {leaf ._} (write-C s addr val) = MemWriteResp
Response  Mem {leaf ._} (read-C s addr)      = MemReadResp
next      Mem {leaf ._} (alloc-C s) alloc-success = leaf $ suc s
next      Mem {leaf ._} (alloc-C s) alloc-fail    = leaf $ s
next      Mem {leaf ._} (dealloc-C s)        r    = leaf $ s
next      Mem {leaf ._} (write-C s addr val) r    = leaf $ s
next      Mem {leaf ._} (read-C s addr)      r    = leaf $ s

mkSmartConstructor : ∀{s}(c : Command Mem s) → FreeMonad Mem (StrongAtkey (Response Mem {s} c) (next Mem {s} c)) s
mkSmartConstructor {s} c = Invoke-FM c λ r → Return-FM (StrongV r refl)

mkSmartConstructor′ : ∀{s}(c : Command Mem s) s′
                    → (∀ r → next Mem {s} c r ≡ s′)
                    → FreeMonad Mem (Atkey (Response Mem {s} c) s′) s
mkSmartConstructor′ {s} c s′ pf = Invoke-FM c λ r → Return-FM (transport (Atkey (Response Mem {s} c) s′) (sym $ pf r) (V r))

alloc : ∀ s → FreeMonad Mem (StrongAtkey MemAllocResp (next Mem {leaf s} (alloc-C s))) (leaf s)
alloc s = mkSmartConstructor {leaf s} (alloc-C s)

dealloc : ∀ s → FreeMonad Mem (StrongAtkey ⊤ (next Mem {leaf (suc s)} (dealloc-C s))) (leaf $ suc s)
dealloc s = mkSmartConstructor (dealloc-C s)

dealloc′ : ∀ s → FreeMonad Mem (Atkey ⊤ (leaf s)) (leaf $ suc s)
dealloc′ s = mkSmartConstructor′ (dealloc-C s) (leaf s) (const refl)

write : ∀ s addr val → FreeMonad Mem (StrongAtkey MemWriteResp (next Mem {leaf s} (write-C s addr val))) (leaf s)
write s addr val = mkSmartConstructor (write-C s addr val)

-- We know that write can never change the state.  Can we encode this?
write′ : ∀ s addr val → FreeMonad Mem (Atkey MemWriteResp (leaf s)) (leaf s)
write′ s addr val = mkSmartConstructor′ (write-C s addr val) (leaf s) (const refl)

read : ∀ s addr → FreeMonad Mem (StrongAtkey MemReadResp (next Mem {leaf s} (read-C s addr))) (leaf s)
read s addr = mkSmartConstructor (read-C s addr)

read′ : ∀ s addr → FreeMonad Mem (Atkey MemReadResp (leaf s)) (leaf s)
read′ s addr = mkSmartConstructor′ (read-C s addr) (leaf s) (const refl)

inc : ∀ s addr → FreeMonad Mem (Atkey ⊤ (leaf s)) (leaf s)
inc s addr = read′ s addr >>=ⁱ λ {
                 (V (read-success n))   → fmapⁱ (λ { (V _) → V tt }) (write′ s addr n) ;
                 (V read-out-of-bounds) → returnⁱ (V tt)
             }

modify-vec : ∀{n} → Nat → Nat → Vec Nat n → Maybe (Vec Nat n)
modify-vec addr val [] = nothing
modify-vec zero val (v ∷ vs) = just $ val ∷ vs
modify-vec (suc addr) val (v ∷ vs) = fmap (_∷_ v) $ modify-vec addr val vs

lookup-vec : ∀{n} → Nat → Vec Nat n → Maybe Nat
lookup-vec addr [] = nothing 
lookup-vec zero (x ∷ xs) = just x
lookup-vec (suc addr) (x ∷ xs) = lookup-vec addr xs

open Implementation

module _ where
  open import Utility.State.Indexed.FromUniverse (Vec Nat)
  eval-direct : Implementation Mem IxState getleaf-BT′
  RunImpl eval-direct {leaf ._} (alloc-C s)          = fmapⁱ (λ { (V _) → StrongV alloc-success refl }) $ modify (_∷_ zero) 
  RunImpl eval-direct {leaf ._} (dealloc-C s)        = fmapⁱ (λ { (V _) → StrongV tt refl }) $ modify λ { (_ ∷ v) → v }
  RunImpl eval-direct {leaf ._} (write-C s addr val) = get >>=ⁱ lem
    where lem : ∀{s′} → Atkey (Vec Nat s) s s′ → IxState (StrongAtkey MemWriteResp (getleaf-BT′ ∘′ next Mem {leaf s} (write-C s addr val))) s′
          lem (V v) with modify-vec addr val v
          lem (V v) | nothing = returnⁱ (StrongV write-out-of-bounds refl)
          lem (V v) | just _ = returnⁱ (StrongV write-success refl)
  RunImpl eval-direct {leaf ._} (read-C s addr)      = get >>=ⁱ lem
    where lem : ∀{s′} → Atkey (Vec Nat s) s s′ → IxState (StrongAtkey MemReadResp (getleaf-BT′ ∘′ next Mem {leaf s} (read-C s addr))) s′
          lem (V v) with lookup-vec addr v
          lem (V v) | nothing = returnⁱ (StrongV read-out-of-bounds refl)
          lem (V v) | just k = returnⁱ (StrongV (read-success k) refl)
