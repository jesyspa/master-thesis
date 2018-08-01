{-# OPTIONS --type-in-type #-}
open import Syntactic.Enumeration
module Syntactic.Reorder (ST : Set){{EST : Enumeration ST}} where

open import ThesisPrelude
open import Algebra.FunExt
open import Syntactic.CommandStructure
open import Syntactic.EnumerationInstances
open import Syntactic.CryptoExpr ST
open FM CryptoExprCS
open import Syntactic.StateBounds ST
open import Syntactic.Logic ST
open import Syntactic.LogicDerived ST
open import Utility.Vector.Definition
open import Utility.Vector.Functions
open import Utility.Vector.Props
open import Utility.List.Elem.Definition
open import Utility.List.Elem.Map
open import Utility.Num

open CommandStructure
open Enumeration {{...}}
     
maximum : List Nat → Nat
maximum = foldr max zero

postulate
  maximum-Max : ∀{n xs} → n ∈ xs → n ≤ maximum xs

maximumOf : ∀{A}{{_ : Enumeration A}}
          → (f : A → Nat)
          → Nat
maximumOf f = maximum (map f Enumerate)

maximumOf-Max : ∀{A}{{_ : Enumeration A}}
              → (f : A → Nat)
              → ∀ a → f a ≤ maximumOf f
maximumOf-Max f a = maximum-Max (map-preserves-in f _ _ (EnumerateComplete a)) 

instance
  EnumerationResponses : ∀ c → Enumeration (Response CryptoExprCS c)
  EnumerationResponses (Uniform n) = EnumerationBitVec n
  EnumerationResponses  GetState = EST
  EnumerationResponses (SetState _) = it

compute-max-CA : CommandAlgebra Nat
compute-max-CA c cont = maximumOf cont

get-randomness-Cmd : CryptoExprCmd → Nat
get-randomness-Cmd (Uniform n)  = n
get-randomness-Cmd  GetState    = zero
get-randomness-Cmd (SetState _) = zero

get-randomness-CA : CommandAlgebra Nat
get-randomness-CA = augment-algebra get-randomness-Cmd _+_ compute-max-CA

get-randomness : ∀{A} → CryptoExpr A → Nat
get-randomness = fold-algebra get-randomness-CA (const zero)

get-randomness′ : ∀{A} → CryptoExpr A → ST → Nat
get-randomness′ (Return-FM _)                  st = zero
get-randomness′ (Invoke-FM (Uniform n) cont)   st = n + maximumOf (λ v → get-randomness′ (cont v) st)
get-randomness′ (Invoke-FM  GetState cont)     st = get-randomness′ (cont st) st
get-randomness′ (Invoke-FM (SetState st) cont) _  = get-randomness′ (cont tt) st

data EnoughRandomness : ∀{A} → ST → Nat → CryptoExpr A → Set₁ where
  Return-ER   : ∀{A n st} (a : A) → EnoughRandomness st n (Return-FM a)
  Uniform-ER  : ∀{A n k m st} 
              → m ≡ n + k
              → {cont : BitVec n → CryptoExpr A}
              → ((v : BitVec n) → EnoughRandomness st k (cont v))
              → EnoughRandomness st m (Invoke-FM (Uniform n) cont)
  GetState-ER : ∀{A n st} 
              → {cont : ST → CryptoExpr A}
              → (er : EnoughRandomness st n (cont st))
              → EnoughRandomness st n (Invoke-FM GetState cont)
  SetState-ER : ∀{A n st st′} 
              → {cont : ⊤ → CryptoExpr A}
              → (er : EnoughRandomness st′ n (cont tt))
              → EnoughRandomness st n (Invoke-FM (SetState st′) cont)

ER-pi : ∀{A st k}{ce : CryptoExpr A}
      → (er es : EnoughRandomness st k ce)
      → er ≡ es
ER-pi (Return-ER a) (Return-ER .a) = refl
ER-pi (Uniform-ER {n = n} eq cons) (Uniform-ER {n = .n} ep cont)
  rewrite add-Inj n (eq ʳ⟨≡⟩ ep) with eq | ep
... | refl | refl = cong (Uniform-ER refl) $ dep-fun-ext _ _ λ a → ER-pi (cons a) (cont a)
ER-pi (GetState-ER cons) (GetState-ER cont) = cong GetState-ER $ ER-pi cons cont
ER-pi (SetState-ER cons) (SetState-ER cont) = cong SetState-ER $ ER-pi cons cont

Weaken-ER : ∀{A n k st} → (n ≤ k) → {ce : CryptoExpr A}
          → EnoughRandomness st n ce
          → EnoughRandomness st k ce
Weaken-ER le (Return-ER a) = Return-ER a
Weaken-ER {n = n} {k = k} (diff i eq) (Uniform-ER {n = a} {k = b} refl cont)
  rewrite ≤N-get-eq (diff i eq)
        | add-assoc a b i
        = Uniform-ER refl λ v → Weaken-ER (diff i auto) (cont v)
Weaken-ER le (GetState-ER er) = GetState-ER (Weaken-ER le er)
Weaken-ER le (SetState-ER er) = SetState-ER (Weaken-ER le er)

matchUniform-ER : ∀{A n k m st}{cont : BitVec n → CryptoExpr A}
                → n + k ≡ m
                → EnoughRandomness st m (Invoke-FM (Uniform n) cont)
                → ∀ v → EnoughRandomness st k (cont v)
matchUniform-ER {n = n} eq (Uniform-ER refl pf) rewrite add-Inj n eq = pf
matchGetState-ER : ∀{A k st}{cont : ST → CryptoExpr A}
                 → EnoughRandomness st k (Invoke-FM GetState cont)
                 → EnoughRandomness st k (cont st)
matchGetState-ER (GetState-ER pf) = pf
matchSetState-ER : ∀{A k st st′}{cont : ⊤ → CryptoExpr A}
                 → EnoughRandomness st′ k (Invoke-FM (SetState st) cont)
                 → EnoughRandomness st k (cont tt)
matchSetState-ER (SetState-ER pf) = pf

get-final-state : ∀{A k} st (ce : CryptoExpr A) → EnoughRandomness st k ce → BitVec k → ST
get-final-state st (Return-FM _) _ v = st
get-final-state st (Invoke-FM (Uniform n) cont) (Uniform-ER refl er) v
  = let l , r = vsplit n v
    in get-final-state st (cont l) (er l) r
get-final-state st (Invoke-FM  GetState cont) er v = get-final-state st (cont st) (matchGetState-ER er) v
get-final-state _  (Invoke-FM (SetState st′) cont) er v = get-final-state st′ (cont tt) (matchSetState-ER er) v

get-final-state-Weaken : ∀{A k k′ st}(le : k ≤ k′){ce : CryptoExpr A}
                       → (er : EnoughRandomness st k ce)
                       → (v : BitVec k′)
                       → get-final-state st ce er (vtake′ k le v) ≡ get-final-state st ce (Weaken-ER le er) v
get-final-state-Weaken le (Return-ER a) v = refl
get-final-state-Weaken {k = k} {k′} (diff i refl) (Uniform-ER {n = n} {k = j} refl cont) v =
  let v′ : BitVec (n + (i + j))
      v′ = transport BitVec auto v
      w = vtake′ k (diff i refl) v
      l , r = vsplit n v′
      l′ , r′ = vsplit n w
      l≡l′ : l ≡ l′
      l≡l′ = {!vsplit-vtake-fst ? ? ? ? ?!}
      i+j≡j+i : i + j ≡ j + i
      i+j≡j+i = auto
      r≡r′ : vtake j (transport BitVec i+j≡j+i r) ≡ r′
      r≡r′ = {!!}
  in
  get-final-state _ _ (cont l′) r′ 
    ≡⟨ {!!} ⟩
  get-final-state _ _ (cont l) r′ 
    ≡⟨ {!!} ⟩
  get-final-state _ _ (Weaken-ER (diff i refl) {!cont l!}) r
  ∎
get-final-state-Weaken le (GetState-ER er) v = get-final-state-Weaken le er v
get-final-state-Weaken le (SetState-ER er) v = get-final-state-Weaken le er v

get-randomness′-Sound : ∀{A} st (ce : CryptoExpr A) → EnoughRandomness st (get-randomness′ ce st) ce
get-randomness′-Sound st (Return-FM a) = Return-ER a
get-randomness′-Sound st (Invoke-FM (Uniform n) cont) = Uniform-ER refl λ v → Weaken-ER (maximumOf-Max _ v) (get-randomness′-Sound st (cont v))
get-randomness′-Sound st (Invoke-FM  GetState cont) = GetState-ER (get-randomness′-Sound st (cont st))
get-randomness′-Sound st (Invoke-FM (SetState st′) cont) = SetState-ER (get-randomness′-Sound st′ (cont tt)) 

get-final-state′ : ∀{A} (ce : CryptoExpr A)(st : ST) → BitVec (get-randomness′ ce st) → ST
get-final-state′ ce st v = get-final-state st ce (get-randomness′-Sound st ce) v

get-result : ∀{A k} st (ce : CryptoExpr A) → EnoughRandomness st k ce → BitVec k → A
get-result st (Return-FM a) er v = a
get-result st (Invoke-FM (Uniform n) cont) (Uniform-ER refl er) v
  = let l , r = vsplit n v
     in get-result st (cont l) (er l) r 
get-result st (Invoke-FM  GetState cont) (GetState-ER er) v
  = get-result st (cont st) er v
get-result st (Invoke-FM (SetState st′) cont) (SetState-ER er) v
  = get-result st′ (cont tt) er v

get-result-Weaken : ∀{A k k′ st}(le : k ≤ k′){ce : CryptoExpr A}
                  → (er : EnoughRandomness st k ce)
                  → (v : BitVec k′)
                  → get-result st ce er (vtake′ k le v) ≡ get-result st ce (Weaken-ER le er) v
get-result-Weaken = {!!}

get-result′ : ∀{A}(ce : CryptoExpr A)(st : ST) → BitVec (get-randomness′ ce st) → A
get-result′ ce st v = get-result st ce (get-randomness′-Sound st ce) v

canonic-form′ : ∀{A} → (n-fun : ST → Nat) → ((st : ST) → BitVec (n-fun st) → ST) → ((st : ST) → BitVec (n-fun st) → A) → CryptoExpr A
canonic-form′ n-fun st-fun ret-fun
  = Invoke-FM GetState λ st →
    Invoke-FM (Uniform (n-fun st)) λ v →
    Invoke-FM (SetState (st-fun st v)) λ _ →
    Return-FM (ret-fun st v)

canonic-form : ∀{A} → CryptoExpr A → CryptoExpr A
canonic-form ce = canonic-form′ (get-randomness′ ce) (get-final-state′ ce) (get-result′ ce)


canonic-form-Sound : ∀{A} → (ce : CryptoExpr A) → canonic-form ce ≡E ce
canonic-form-Sound (Return-FM a) =
  canonic-form′ (const zero) (λ st _ → st) (λ _ _ → a)
    ≡E⟨ refl-≡E ⟩
  (Invoke-FM GetState λ st → Invoke-FM (Uniform zero) λ _ → Invoke-FM (SetState st) λ _ → Return-FM a )
    ≡E⟨ cong≡E-invoke _ (λ st → trivial-uniform _) ⟩ʳ
  (Invoke-FM GetState λ st → Invoke-FM (SetState st) λ _ → Return-FM a )
    ≡E⟨ relate-getset _ ⟩
  (Invoke-FM GetState λ st → Return-FM a )
    ≡E⟨ trivial-getstate _ ⟩ʳ
  Return-FM a
  ∎E
canonic-form-Sound (Invoke-FM (Uniform n) cont) =
  canonic-form (Invoke-FM (Uniform n) cont)
    ≡E⟨ refl-≡E ⟩
  (Invoke-FM GetState λ st →
   Invoke-FM (Uniform (n + maximumOf (λ w → get-randomness′ (cont w) st))) λ v →
   let l , r = vsplit n v
       wer = Weaken-ER (maximumOf-Max (λ w → get-randomness′ (cont w) st) l) (get-randomness′-Sound st (cont l))
   in
   Invoke-FM (SetState (get-final-state st (cont l) wer r)) λ _ →
   Return-FM (get-result st (cont l) wer r))
    ≡E⟨ (cong≡E-invoke _ λ st →
         cong≡E-invoke _ λ v →
         let l , r = vsplit n v
             le = maximumOf-Max (λ w → get-randomness′ (cont w) st) l
             er = get-randomness′-Sound st (cont l) in
         reflˡ-≡E $ cong₂ (λ e₁ e₂ → Invoke-FM (SetState e₁) λ _ → Return-FM e₂)
                          (get-final-state-Weaken le er r)
                          (get-result-Weaken le er r)) ⟩ʳ
  (Invoke-FM GetState λ st →
   Invoke-FM (Uniform $ n + maximumOf (λ w → get-randomness′ (cont w) st)) λ v →
   let l , r = vsplit n v
       r′ = vtake′ (get-randomness′ (cont l) st) (maximumOf-Max (λ w → get-randomness′ (cont w) st) l) r in
   Invoke-FM (SetState (get-final-state′ (cont l) st r′)) λ _ →
   Return-FM (get-result′ (cont l) st r′))
    ≡E⟨ ((cong≡E-invoke _ λ st → unmerge-uniform _ _ _)) ⟩ʳ
  (Invoke-FM GetState λ st →
   Invoke-FM (Uniform n) λ l →
   Invoke-FM (Uniform (maximumOf (λ w → get-randomness′ (cont w) st))) λ r →
   let r′ = vtake′ (get-randomness′ (cont l) st) (maximumOf-Max (λ w → get-randomness′ (cont w) st) l) r in
   Invoke-FM (SetState (get-final-state′ (cont l) st r′)) λ _ →
   Return-FM (get-result′ (cont l) st r′))
    ≡E⟨ (cong≡E-invoke _ λ st →
         cong≡E-invoke _ λ l →
         extend-uniform′ (maximumOf-Max (λ w → get-randomness′ (cont w) st) l) _) ⟩ʳ
  (Invoke-FM GetState λ st →
   Invoke-FM (Uniform n) λ l →
   Invoke-FM (Uniform (get-randomness′ (cont l) st)) λ r →
   Invoke-FM (SetState (get-final-state′ (cont l) st r)) λ _ →
   Return-FM (get-result′ (cont l) st r))
    ≡E⟨ reorder-onewrite-base _ _ Uniform-NAR Uniform-NAW _ ⟩
  Invoke-FM (Uniform n) (λ l → canonic-form (cont l))
    ≡E⟨ cong≡E-invoke _ (λ l → canonic-form-Sound (cont l)) ⟩
  Invoke-FM (Uniform n) cont
  ∎E
canonic-form-Sound (Invoke-FM  GetState cont) =
  canonic-form (Invoke-FM GetState cont)
    ≡E⟨ join-getstate _ ⟩ʳ
  Invoke-FM GetState (λ st → canonic-form (cont st))
    ≡E⟨ cong≡E-invoke _ (λ st → canonic-form-Sound (cont st)) ⟩
  Invoke-FM GetState cont
  ∎E
canonic-form-Sound (Invoke-FM (SetState st) cont) =
  canonic-form (Invoke-FM (SetState st) cont)
    ≡E⟨ trivial-getstate _ ⟩ʳ
  (Invoke-FM (Uniform (get-randomness′ (cont tt) st)) λ v →
   Invoke-FM (SetState (get-final-state′ (cont tt) st v)) λ _ →
   Return-FM (get-result′ (cont tt) st v))
    ≡E⟨ cong≡E-invoke _ (λ v → join-setstate _ _ _) ⟩ʳ
  (Invoke-FM (Uniform (get-randomness′ (cont tt) st)) λ v →
   Invoke-FM (SetState st) λ t →
   Invoke-FM (SetState (get-final-state′ (cont t) st v)) λ _ →
   Return-FM (get-result′ (cont t) st v))
    ≡E⟨ reorder-onewrite-base _ _ Uniform-NAR Uniform-NAW _ ⟩ʳ
  (Invoke-FM (SetState st) λ t →
   Invoke-FM (Uniform (get-randomness′ (cont t) st)) λ v →
   Invoke-FM (SetState (get-final-state′ (cont t) st v)) λ _ →
   Return-FM (get-result′ (cont t) st v))
    ≡E⟨ relate-setget st _ ⟩ʳ
  Invoke-FM (SetState st) (λ t → canonic-form (cont t))
    ≡E⟨ cong≡E-invoke _ (λ { tt → canonic-form-Sound (cont tt) }) ⟩
  Invoke-FM (SetState st) cont
  ∎E
