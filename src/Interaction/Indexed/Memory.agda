module Interaction.Indexed.Memory where

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
  write-C   : ∀ s → (addr : Fin s) → (val : Nat) → MemCmd s
  read-C    : ∀ s → (addr : Fin s) → MemCmd s

data MemAllocResp : Set where
  alloc-success : MemAllocResp
  alloc-fail    : MemAllocResp

open InteractionStructure
Mem : IStruct (Leaf Nat)
Command   Mem (leaf  s) = MemCmd s
Response  Mem {leaf ._} (alloc-C s)   = MemAllocResp
Response  Mem {leaf ._} (dealloc-C s) = ⊤
Response  Mem {leaf ._} (write-C s addr val) = ⊤
Response  Mem {leaf ._} (read-C s addr)      = Nat
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

write : ∀ s addr val → FreeMonad Mem (StrongAtkey ⊤ (next Mem {leaf s} (write-C s addr val))) (leaf s)
write s addr val = mkSmartConstructor (write-C s addr val)

-- We know that write can never change the state.  Can we encode this?
write′ : ∀ s addr val → FreeMonad Mem (Atkey ⊤ (leaf s)) (leaf s)
write′ s addr val = mkSmartConstructor′ (write-C s addr val) (leaf s) (const refl)

read : ∀ s addr → FreeMonad Mem (StrongAtkey Nat (next Mem {leaf s} (read-C s addr))) (leaf s)
read s addr = mkSmartConstructor (read-C s addr)

read′ : ∀ s addr → FreeMonad Mem (Atkey Nat (leaf s)) (leaf s)
read′ s addr = mkSmartConstructor′ (read-C s addr) (leaf s) (const refl)

inc : ∀ s (addr : Fin s) → FreeMonad Mem (Atkey ⊤ (leaf s)) (leaf s)
inc s addr = read′ s addr >>=ⁱ λ { (V n) → write′ s addr n }

modify-vec : ∀{n} → Fin n → Nat → Vec Nat n → Vec Nat n
modify-vec () val []
modify-vec zero val (x ∷ xs) = val ∷ xs
modify-vec (suc addr) val (x ∷ xs) = x ∷ modify-vec addr val xs

lookup-vec : ∀{n} → Fin n → Vec Nat n → Nat
lookup-vec () []
lookup-vec zero (x ∷ xs) = x
lookup-vec (suc addr) (x ∷ xs) = lookup-vec addr xs

open Implementation

module _ where
  open import Utility.State.Indexed.FromUniverse (Vec Nat)
  eval-direct : Implementation Mem IxState getleaf-BT′
  RunImpl eval-direct {leaf ._} (alloc-C s)          = fmapⁱ (λ { (V _) → StrongV alloc-success refl }) $ modify (_∷_ zero) 
  RunImpl eval-direct {leaf ._} (dealloc-C s)        = fmapⁱ (λ { (V _) → StrongV tt refl }) $ modify λ { (_ ∷ v) → v }
  RunImpl eval-direct {leaf ._} (write-C s addr val) = fmapⁱ (λ { (V _) → StrongV tt refl }) $ modify (modify-vec addr val)
  RunImpl eval-direct {leaf ._} (read-C s addr)      = fmapⁱ (λ { (V r) → StrongV (lookup-vec addr r) refl }) $ modify id

  eval-bounded : ∀ b → Implementation Mem IxState getleaf-BT′ 
  RunImpl (eval-bounded b) {leaf._} (alloc-C s)          = if isLess (compare b s) 
                                                           then fmapⁱ (λ { (V _) → StrongV alloc-success refl }) (modify (_∷_ zero))
                                                           else returnⁱ (StrongV alloc-fail refl)
  RunImpl (eval-bounded b) {leaf._} (dealloc-C s)        = fmapⁱ (λ { (V _) → StrongV tt refl }) $ modify λ { (_ ∷ v) → v }
  RunImpl (eval-bounded b) {leaf._} (write-C s addr val) = fmapⁱ (λ { (V _) → StrongV tt refl }) $ modify (modify-vec addr val)
  RunImpl (eval-bounded b) {leaf._} (read-C s addr)      = fmapⁱ (λ { (V r) → StrongV (lookup-vec addr r) refl }) $ modify id

