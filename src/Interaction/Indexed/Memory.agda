module Interaction.Indexed.Memory where

open import ThesisPrelude
open import Algebra.Lift
open import Algebra.Indexed.Monad
open import Algebra.Indexed.Atkey
open import Interaction.Indexed.InteractionStructure
open import Interaction.Indexed.FreeMonad
open import Interaction.Indexed.Implementation
open import Utility.State.Indexed.Definition {lzero}

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

modify-vec : ∀{n} → Fin n → Nat → Vec Nat n → Vec Nat n
modify-vec () val []
modify-vec zero val (x ∷ xs) = val ∷ xs
modify-vec (suc addr) val (x ∷ xs) = x ∷ modify-vec addr val xs

lookup-vec : ∀{n} → Fin n → Vec Nat n → Nat
lookup-vec () []
lookup-vec zero (x ∷ xs) = x
lookup-vec (suc addr) (x ∷ xs) = lookup-vec addr xs

eval-direct : Implementation Mem IxState (Vec Nat)
eval-direct {.s}       (alloc-C s)          = fmapⁱ (λ { (V (lift _)) → StrongV alloc-success refl }) $ modify (_∷_ zero)
eval-direct {.(suc s)} (dealloc-C s)        = fmapⁱ (λ { (V (lift _)) → StrongV tt refl }) $ modify λ { (_ ∷ v) → v }
eval-direct {.s}       (write-C s addr val) = fmapⁱ (λ { (V (lift _)) → StrongV tt refl }) $ modify (modify-vec addr val)
eval-direct {.s}       (read-C s addr)      = fmapⁱ (λ { (V (lift r)) → StrongV (lookup-vec addr r) refl }) $ modify id

eval-bounded : ∀ b → Implementation Mem IxState (Vec Nat)
eval-bounded b {.s}       (alloc-C s)          = if isLess (compare b s) 
                                                 then fmapⁱ (λ { (V (lift _)) → StrongV alloc-success refl }) (modify (_∷_ zero))
                                                 else returnⁱ (StrongV alloc-fail refl)
eval-bounded b {.(suc s)} (dealloc-C s)        = fmapⁱ (λ { (V (lift _)) → StrongV tt refl }) $ modify λ { (_ ∷ v) → v }
eval-bounded b {.s}       (write-C s addr val) = fmapⁱ (λ { (V (lift _)) → StrongV tt refl }) $ modify (modify-vec addr val)
eval-bounded b {.s}       (read-C s addr)      = fmapⁱ (λ { (V (lift r)) → StrongV (lookup-vec addr r) refl }) $ modify id

module _ where
  open import Algebra.Indexed.Reindexing (Vec Nat) IxState {{it}} renaming (Reindexed to VecState)
  modifyVec : ∀{n k} → (f : Vec Nat n → Vec Nat k) → VecState (Atkey (Lift (Vec Nat k)) k) n
  modifyVec = ?
