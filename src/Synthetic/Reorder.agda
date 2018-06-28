{-# OPTIONS --type-in-type #-}
open import Synthetic.Enumeration
module Synthetic.Reorder (ST : Set){{EST : Enumeration ST}} where

open import ThesisPrelude
open import Synthetic.CommandStructure
open import Synthetic.EnumerationInstances
open import Synthetic.CryptoExpr ST
open FM CryptoExprCS
open import Synthetic.StateBounds ST
open import Synthetic.Logic ST
open import Synthetic.LogicDerived ST
open import Utility.Vector.Definition
open import Utility.Vector.Functions
open import Utility.List.Elem.Definition
open import Utility.List.Elem.Map

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
  Uniform-ER  : ∀{A n k st} 
              → {cont : BitVec n → CryptoExpr A}
              → ((v : BitVec n) → EnoughRandomness st k (cont v))
              → EnoughRandomness st (n + k) (Invoke-FM (Uniform n) cont)
  GetState-ER : ∀{A n st} 
              → {cont : ST → CryptoExpr A}
              → (er : EnoughRandomness st n (cont st))
              → EnoughRandomness st n (Invoke-FM GetState cont)
  SetState-ER : ∀{A n st st′} 
              → {cont : ⊤ → CryptoExpr A}
              → (er : EnoughRandomness st′ n (cont tt))
              → EnoughRandomness st n (Invoke-FM (SetState st′) cont)

postulate
  Weaken-ER : ∀{A n k st} → (n ≤ k) → {ce : CryptoExpr A}
            → EnoughRandomness st n ce
            → EnoughRandomness st k ce

get-final-state : ∀{A k} st (ce : CryptoExpr A) → EnoughRandomness st k ce → BitVec k → ST
get-final-state st (Return-FM _) (Return-ER _) v = st
get-final-state st (Invoke-FM (Uniform n) cont) (Uniform-ER er) v
  = let l , r = vsplit n v
    in get-final-state st (cont l) (er l) r
get-final-state st (Invoke-FM  GetState cont) (GetState-ER er) v = get-final-state st (cont st) er v
get-final-state _  (Invoke-FM (SetState st′) cont) (SetState-ER er) v = get-final-state st′ (cont tt) er v

get-randomness′-Sound : ∀{A} st (ce : CryptoExpr A) → EnoughRandomness st (get-randomness′ ce st) ce
get-randomness′-Sound st (Return-FM a) = Return-ER a
get-randomness′-Sound st (Invoke-FM (Uniform n) cont) = Uniform-ER λ v → Weaken-ER (maximumOf-Max _ v) (get-randomness′-Sound st (cont v))
get-randomness′-Sound st (Invoke-FM  GetState cont) = GetState-ER (get-randomness′-Sound st (cont st))
get-randomness′-Sound st (Invoke-FM (SetState st′) cont) = SetState-ER (get-randomness′-Sound st′ (cont tt)) 

get-final-state′ : ∀{A} (ce : CryptoExpr A)(st : ST) → BitVec (get-randomness′ ce st) → ST
get-final-state′ ce st v = get-final-state st ce (get-randomness′-Sound st ce) v

get-result : ∀{A k} st (ce : CryptoExpr A) → EnoughRandomness st k ce → BitVec k → A
get-result st (Return-FM a) er v = a
get-result st (Invoke-FM (Uniform n) cont) (Uniform-ER er) v
  = let l , r = vsplit n v
     in get-result st (cont l) (er l) r 
get-result st (Invoke-FM  GetState cont) (GetState-ER er) v
  = get-result st (cont st) er v
get-result st (Invoke-FM (SetState st′) cont) (SetState-ER er) v
  = get-result st′ (cont tt) er v

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

uniform-lemma : ∀{A n k} st (cont : BitVec n → CryptoExpr A)
              → (er : ∀ v → EnoughRandomness st k (cont v))
              → (Invoke-FM (Uniform (n + k)) λ v →
                 let l , r = vsplit n v in
                 Invoke-FM (SetState (get-final-state st (cont l) (er l) r)) λ _ →
                 Return-FM (get-result st (cont l) (er l) r))
               ≡E
                (Invoke-FM (Uniform n) λ l →
                 Invoke-FM (Uniform k) λ r →
                 Invoke-FM (SetState (get-final-state st (cont l) (er l) r)) λ _ →
                 Return-FM (get-result st (cont l) (er l) r))
uniform-lemma st cont er = sym-≡E $ unmerge-uniform _ _ _

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
    ≡E⟨ cong≡E-invoke _ (λ st → unmerge-uniform _ _ _)  ⟩ʳ
  (Invoke-FM GetState λ st →
   Invoke-FM (Uniform n) λ l →
   Invoke-FM (Uniform (maximumOf (λ w → get-randomness′ (cont w) st))) λ r →
   let wer = Weaken-ER (maximumOf-Max (λ w → get-randomness′ (cont w) st) l) (get-randomness′-Sound st (cont l)) in
   Invoke-FM (SetState (get-final-state st (cont l) wer r)) λ _ →
   Return-FM (get-result st (cont l) wer r))
    ≡E⟨ {!!} ⟩
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
