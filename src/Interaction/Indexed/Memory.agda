module Interaction.Indexed.Memory where

open import ThesisPrelude
open import Algebra.Indexed.Monad
open import Algebra.Indexed.Atkey
open import Interaction.Indexed.InteractionStructure
open import Interaction.Indexed.FreeMonad

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
Mem : IStruct Nat
Command   Mem = MemCmd
Response  Mem (alloc-C s)   = MemAllocResp
Response  Mem (dealloc-C s) = ⊤
Response  Mem (write-C s addr val) = ⊤
Response  Mem (read-C s addr)      = Nat
next      Mem {c = alloc-C s} alloc-success = suc s
next      Mem {c = alloc-C s} alloc-fail    = s
next      Mem {c = dealloc-C s}        r    = s
next      Mem {c = write-C s addr val} r    = s
next      Mem {c = read-C s addr}      r    = s

mkSmartConstructor : ∀{s}(c : Command Mem s) → FreeMonad Mem (StrongAtkey (Response Mem c) (next Mem {c = c})) s
mkSmartConstructor c = Invoke-FM c λ r → Return-FM (StrongV r refl)

mkSmartConstructor′ : ∀{s}(c : Command Mem s) s′
                    → (∀ r → next Mem {c = c} r ≡ s′)
                    → FreeMonad Mem (Atkey (Response Mem c) s′) s
mkSmartConstructor′ c s′ pf = Invoke-FM c λ r → Return-FM (transport (Atkey (Response Mem c) s′) (sym $ pf r) (V r))

alloc : ∀ s → FreeMonad Mem (StrongAtkey MemAllocResp (next Mem {c = alloc-C s})) s
alloc s = mkSmartConstructor (alloc-C s)

dealloc : ∀ s → FreeMonad Mem (StrongAtkey ⊤ (next Mem {c = dealloc-C s})) (suc s)
dealloc s = mkSmartConstructor (dealloc-C s)

dealloc′ : ∀ s → FreeMonad Mem (Atkey ⊤ s) (suc s)
dealloc′ s = mkSmartConstructor′ (dealloc-C s) s (const refl)

write : ∀ s addr val → FreeMonad Mem (StrongAtkey ⊤ (next Mem {c = write-C s addr val})) s
write s addr val = mkSmartConstructor (write-C s addr val)

-- We know that write can never change the state.  Can we encode this?
write′ : ∀ s addr val → FreeMonad Mem (Atkey ⊤ s) s
write′ s addr val = mkSmartConstructor′ (write-C s addr val) s (const refl)

read : ∀ s addr → FreeMonad Mem (StrongAtkey Nat (next Mem {c = read-C s addr})) s
read s addr = mkSmartConstructor (read-C s addr)

read′ : ∀ s addr → FreeMonad Mem (Atkey Nat s) s
read′ s addr = mkSmartConstructor′ (read-C s addr) s (const refl)

inc : ∀ s (addr : Fin s) → FreeMonad Mem (Atkey ⊤ s) s
inc s addr = read′ s addr >>=ⁱ λ { (V n) → write′ s addr n }
