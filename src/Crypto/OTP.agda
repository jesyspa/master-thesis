import Probability.Class as PC
import Probability.PropsClass as PPC
module Crypto.OTP (Q : Set) {{PQ : PC.Probability Q}} {{PPQ : PPC.ProbabilityProps Q}} where

open import ThesisPrelude
open import Crypto.Syntax
open import Crypto.Props
open import Utility.Vector
open import Utility.Bool
open import Probability.Class
open import Probability.PropsClass Q
open Probability PQ
open ProbabilityProps PPQ
open import Distribution.Class
open import Distribution.List Q
open import Distribution.PropsClass ListDist {{DistMonadListDist}}
open import Distribution.Reasoning ListDist {{DistMonadListDist}}
open import Algebra.MonadProps ListDist
import Algebra.MonadProps CryptoExpr {{MonadCryptoExpr}} as CEMP 
open import Crypto.Valuation ListDist {{DistMonadListDist}}
open import Crypto.ValuationProps ListDist {{DistMonadListDist}}
open import Crypto.Schemes
open import Crypto.Reasoning ListDist {{DistMonadListDist}}
open import Crypto.CoinExamples ListDist {{DistMonadListDist}}
open import Crypto.SimpleEAV
open import Probability.Class
open DistMonad DistMonadListDist
open DistMonadProps DistMonadPropsListDist
open MonadProps is-monad

OTP : (n : Nat) → EncScheme
OTP n = enc-scheme (BitVec n) 
                   (BitVec n) 
                   (BitVec n) 
                   (uniform-expr n)
                   (λ k pt → return (bitvec-xor k pt) )
                   (λ k ct → bitvec-xor k ct)
                   (λ {k} {pt} → cong return (bitvec-xor-self-inverse k pt))


OTP-is-IND-EAV : ∀{n}(A : SimpleEavAdv (OTP n))
               → coin ≡D ⟦ simple-IND-EAV (OTP n) A ⟧
OTP-is-IND-EAV {n} A =
  coin
    ≡D⟨ coin-interpretation ⟩ˡ
  ⟦ coin-expr ⟧
    ≡D⟨ irrelevance-interpretation (uniform-expr n) coin-expr ⟩
  ⟦( uniform-expr n  >>= λ ct
   → coin-expr )⟧
    ≡D⟨ cong->>= (uniform-expr n)
                 (λ ct → coin-expr)
                 (λ ct → A₂ ct >>= const coin-expr)
                 (λ ct → irrelevance-interpretation (A₂ ct) coin-expr) ⟩
  ⟦( uniform-expr n >>= λ ct
   → A₂ ct          >>= λ b′
   → coin-expr      )⟧
    ≡D⟨ (let expr : (Bool → CryptoExpr Bool) → (BitVec n) → CryptoExpr Bool
             expr f ct = A₂ ct >>= f in
         cong->>= (uniform-expr n)
                  (expr (const coin-expr))
                  (expr (λ b′ → coin-expr >>= λ b → return (nxor b b′)))
                  (λ ct → cong->>= (A₂ ct)
                                   (const coin-expr)
                                   (λ b′ → coin-expr >>= λ b → return (nxor b b′))
                                   coin-sample-2ʳ)) ⟩
  ⟦( uniform-expr n >>= λ k 
   → A₂ k           >>= λ b′
   → coin-expr      >>= λ b
   → return (nxor b b′) )⟧
    ≡D⟨ cong->>= (uniform-expr n)
                 (λ k → A₂ k >>= λ b′ → coin-expr >>= λ b → return (nxor b b′))
                 (λ k → coin-expr >>= λ b → A₂ k >>= λ b′ → return (nxor b b′))
                 (λ k → interchange-interpretation (A₂ k) coin-expr (λ b′ b → return (nxor b b′))) ⟩
  ⟦( uniform-expr n   >>= λ k
   → coin-expr        >>= λ b
   → A₂ k             >>= λ b′
   → return (nxor b b′) )⟧
    ≡D⟨ interchange-interpretation (uniform-expr n) coin-expr
           (λ k b → A₂ k >>= λ b′ → return (nxor b b′)) ⟩
  ⟦( coin-expr      >>= λ b
   → uniform-expr n >>= λ k 
   → A₂ k           >>= λ b′
   → return (nxor b b′) )⟧
    ≡D⟨ irrelevance-interpretation A₁ _ ⟩
  ⟦( A₁             >>= λ m
   → coin-expr      >>= λ b
   → uniform-expr n >>= λ k 
   → A₂ k           >>= λ b′
   → return (nxor b b′) )⟧
    ≡D⟨ cong->>=ˡ A₁
                  (λ m → coin-expr >>= λ b → uniform-expr n >>= λ k → A₂ k >>= λ b′ → return (nxor b b′))
                  (λ m → coin-expr >>= λ b → (if b then uniform-expr n else uniform-expr n) >>= λ k → A₂ k >>= λ b′ → return (nxor b b′))
                  (λ m → cong->>=ˡ coin-expr
                                   (λ b → uniform-expr n >>= λ k → A₂ k >>= λ b′ → return (nxor b b′))
                                   (λ b → (if b then uniform-expr n else uniform-expr n) >>= λ k → A₂ k >>= λ b′ → return (nxor b b′))
                                   (λ b → congl->>=ˡ (uniform-expr n)
                                                     (if b then uniform-expr n else uniform-expr n)
                                                     (λ k → A₂ k >>= λ b′ → return (nxor b b′))
                                                     (cong ⟦_⟧ (if-const-dist b (uniform-expr n))))) ⟩ˡ
  ⟦( A₁                         >>= λ m
   → coin-expr                  >>= λ b
   → (if b then uniform-expr n
           else uniform-expr n) >>= λ k 
   → A₂ k                       >>= λ b′
   → return (nxor b b′))⟧
    ≡D⟨ cong->>= A₁
                 (λ m → coin-expr >>= λ b → (if b then uniform-expr n else uniform-expr n) >>= λ k → A₂ k >>= λ b′ → return (nxor b b′))
                 (λ m → coin-expr >>= λ b → (if b then fmap (bitvec-xorʳ (fst m)) (uniform-expr n) else fmap (bitvec-xorʳ (snd m)) (uniform-expr n)) >>= λ ct → A₂ ct >>= λ b′ → return (nxor b b′))
                 (λ m → cong->>= coin-expr
                                 (λ b → (if b then uniform-expr n else uniform-expr n) >>= λ k → A₂ k >>= λ b′ → return (nxor b b′))
                                 (λ b → (if b then fmap (bitvec-xorʳ (fst m)) (uniform-expr n) else fmap (bitvec-xorʳ (snd m)) (uniform-expr n)) >>= λ ct → A₂ ct >>= λ b′ → return (nxor b b′))
                                 (λ b → congl->>= (if b then uniform-expr n else uniform-expr n)
                                                  (if b then fmap (bitvec-xorʳ (fst m)) (uniform-expr n)
                                                        else fmap (bitvec-xorʳ (snd m)) (uniform-expr n))
                                                  (λ k → A₂ k >>= λ b′ → return (nxor b b′))
                                                  (if-cong b (uniform-expr n) (fmap (bitvec-xorʳ (fst m)) (uniform-expr n))
                                                             (uniform-expr n) (fmap (bitvec-xorʳ (snd m)) (uniform-expr n))
                                                           (uniform-bijection-invariant-interpretation n (bitvec-xorʳ (fst m)) (bitvec-xorʳ-Bij (fst m)))
                                                           (uniform-bijection-invariant-interpretation n (bitvec-xorʳ (snd m)) (bitvec-xorʳ-Bij (snd m))))))⟩
  ⟦( A₁                   >>= λ m
   → coin-expr            >>= λ b
   → (if b then fmap (bitvec-xorʳ (fst m)) (uniform-expr n)
           else fmap (bitvec-xorʳ (snd m)) (uniform-expr n))
                          >>= λ ct 
   → A₂ ct                >>= λ b′
   → return (nxor b b′))⟧
    ≡D⟨ cong->>=ˡ A₁
                  (λ m → coin-expr >>= λ b → (if b then fmap (bitvec-xorʳ (fst m)) (uniform-expr n) else fmap (bitvec-xorʳ (snd m)) (uniform-expr n)) >>= λ ct → A₂ ct >>= λ b′ → return (nxor b b′))
                  (λ m → coin-expr >>= λ b → fmap (bitvec-xorʳ (if b then fst m else snd m)) (uniform-expr n) >>= λ ct → A₂ ct >>= λ b′ → return (nxor b b′))
                  (λ m → cong->>=ˡ coin-expr
                                   (λ b → (if b then fmap (bitvec-xorʳ (fst m)) (uniform-expr n) else fmap (bitvec-xorʳ (snd m)) (uniform-expr n)) >>= λ ct → A₂ ct >>= λ b′ → return (nxor b b′))
                                   (λ b → fmap (bitvec-xorʳ (if b then fst m else snd m)) (uniform-expr n) >>= λ ct → A₂ ct >>= λ b′ → return (nxor b b′))
                                   (λ b → congl->>=ˡ (if b then fmap (bitvec-xorʳ (fst m)) (uniform-expr n) else fmap (bitvec-xorʳ (snd m)) (uniform-expr n))
                                                     (fmap (bitvec-xorʳ (if b then fst m else snd m)) (uniform-expr n))
                                                     (λ ct → A₂ ct >>= λ b′ → return (nxor b b′))
                                                     (cong ⟦_⟧ $ sym $ if-dist b (λ xs → fmap (bitvec-xorʳ xs) (uniform-expr n)) (fst m) (snd m)))) ⟩ˡ
  ⟦( A₁                   >>= λ m
   → coin-expr            >>= λ b
   → fmap (bitvec-xorʳ (if b then fst m else snd m)) (uniform-expr n)
                          >>= λ ct 
   → A₂ ct                >>= λ b′
   → return (nxor b b′))⟧
    ≡D⟨ cong->>=ˡ A₁
                  (λ m → coin-expr >>= λ b → fmap (bitvec-xorʳ (if b then fst m else snd m)) (uniform-expr n) >>= λ ct → A₂ ct >>= λ b′ → return (nxor b b′))
                  (λ m → coin-expr >>= λ b → (uniform-expr n >>= λ k → enc k (if b then fst m else snd m)) >>= λ ct → A₂ ct >>= λ b′ → return (nxor b b′))
                  (λ m → cong->>=ˡ coin-expr
                                   (λ b → fmap (bitvec-xorʳ (if b then fst m else snd m)) (uniform-expr n) >>= λ ct → A₂ ct >>= λ b′ → return (nxor b b′))
                                   (λ b → (uniform-expr n >>= λ k → enc k (if b then fst m else snd m)) >>= λ ct → A₂ ct >>= λ b′ → return (nxor b b′))
                                   (λ b → congl->>=ˡ (fmap (bitvec-xorʳ (if b then fst m else snd m)) (uniform-expr n))
                                                     (uniform-expr n >>= λ k → enc k (if b then fst m else snd m))
                                                     (λ ct → A₂ ct >>= λ b′ → return (nxor b b′))
                                                     (return-simplify-interpretation (λ k → bitvec-xor k (if b then fst m else snd m)) (uniform-expr n)))) ⟩ˡ
  ⟦( A₁                   >>= λ m
   → coin-expr            >>= λ b
   → (uniform-expr n       >>= λ k
   → enc k (if b then fst m else snd m))
                          >>= λ ct 
   → A₂ ct                >>= λ b′
   → return (nxor b b′))⟧
    ≡D⟨ cong->>=ˡ A₁
                  (λ m → coin-expr >>= λ b → (uniform-expr n >>= λ k → enc k (if b then fst m else snd m)) >>= λ ct → A₂ ct >>= λ b′ → return (nxor b b′))
                  (λ m → coin-expr >>= λ b → uniform-expr n >>= λ k → enc k (if b then fst m else snd m) >>= λ ct → A₂ ct >>= λ b′ → return (nxor b b′))
                  (λ m → cong->>=ˡ coin-expr
                                   (λ b → (uniform-expr n >>= λ k → enc k (if b then fst m else snd m)) >>= λ ct → A₂ ct >>= λ b′ → return (nxor b b′))
                                   (λ b → uniform-expr n >>= λ k → enc k (if b then fst m else snd m) >>= λ ct → A₂ ct >>= λ b′ → return (nxor b b′))
                                   (λ b → sym $ >>=-assoc-interpretation (uniform-expr n)
                                                                         (λ k → enc k (if b then fst m else snd m))
                                                                         (λ ct → A₂ ct >>= λ b′ → return (nxor b b′)))) ⟩ˡ
  ⟦( A₁                   >>= λ m
   → coin-expr            >>= λ b
   → uniform-expr n       >>= λ k
   → enc k (if b then fst m else snd m)
                          >>= λ ct 
   → A₂ ct                >>= λ b′
   → return (nxor b b′))⟧
    ≡D⟨ cong->>= A₁
                 (λ m → coin-expr >>= λ b → uniform-expr n >>= λ k → enc k (if b then fst m else snd m) >>= λ ct → A₂ ct >>= λ b′ → return (nxor b b′))
                 (λ m → uniform-expr n >>= λ k → coin-expr >>= λ b → enc k (if b then fst m else snd m) >>= λ ct → A₂ ct >>= λ b′ → return (nxor b b′))
                 (λ m → interchange-interpretation coin-expr (uniform-expr n)
                                                   (λ b k →  enc k (if b then fst m else snd m) >>= λ ct → A₂ ct >>= λ b′ → return (nxor b b′))) ⟩
  ⟦( A₁                   >>= λ m
   → uniform-expr n       >>= λ k
   → coin-expr            >>= λ b
   → enc k (if b then fst m else snd m)
                          >>= λ ct 
   → A₂ ct                >>= λ b′
   → return (nxor b b′))⟧
    ≡D⟨ interchange-interpretation A₁ (uniform-expr n) (λ m k → coin-expr >>= λ b → enc k (if b then fst m else snd m) >>= λ ct → A₂ ct >>= λ b′ → return (nxor b b′)) ⟩
  ⟦( uniform-expr n                     >>= λ k 
   → A₁                                 >>= λ m
   → coin-expr                          >>= λ b
   → enc k (if b then fst m else snd m) >>= λ ct
   → A₂ ct                              >>= λ b′ 
   → return (nxor b b′))⟧
  ∎D
  where
    open SimpleEavAdv A
    open EncScheme (OTP n)
                      
