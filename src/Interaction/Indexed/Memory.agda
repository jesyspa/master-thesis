module Interaction.Indexed.Memory where

open import ThesisPrelude
open import Algebra.Indexed.Atkey
open import Interaction.Indexed.InteractionStructure
open import Interaction.Indexed.FreeMonad

data MemCmd : Nat → Set where
  alloc-C   : ∀{s} → MemCmd s
  dealloc-C : ∀{s} → MemCmd (suc s)
  write-C   : ∀{s} → (addr : Fin s) → (val : Nat) → MemCmd s
  read-C    : ∀{s} → (addr : Fin s) → MemCmd s

data MemAllocResp : Set where
  alloc-success : MemAllocResp
  alloc-fail    : MemAllocResp

open InteractionStructure
Mem : IStruct Nat
Command   Mem = MemCmd
Response  Mem alloc-C   = MemAllocResp
Response  Mem dealloc-C = ⊤
Response  Mem (write-C addr val) = ⊤
Response  Mem (read-C addr)      = Nat
next      Mem {s}        {alloc-C} alloc-success = suc s
next      Mem {s}        {alloc-C} alloc-fail    = s
next      Mem {.(suc s)} {dealloc-C {s}}    r    = s
next      Mem {s}        {write-C addr val} r    = s
next      Mem {s}        {read-C addr} r         = s

alloc : ∀{n} → FreeMonad Mem (DepAtkey (Response Mem (alloc-C {n})) (next Mem {c = alloc-C {n}})) n
alloc = Invoke-FM alloc-C λ r → Return-FM (DepV r) 

