open import ThesisPrelude using (Monoid; Monad)
module Utility.Writer.Transformer {l} (Q : Set l) {{QM : Monoid Q}}
                                      (M : Set l → Set l) {{MM : Monad M}} where

open import ThesisPrelude
open import Algebra.Monoid Q
open import Utility.Writer.Writer Q
open import Utility.Writer.Props Q

open import Algebra.FunctorComposition M Writer as FComp using ()
open import Algebra.ApplicativeComposition M Writer as AComp using ()

open import Algebra.FunctorProps Writer renaming (FunctorProps to WFProps) hiding (fmap-F)
open import Algebra.ApplicativeProps Writer renaming (ApplicativeProps to WAProps; _<*F>_ to _<*W>_) hiding (pure-F)
open import Algebra.MonadProps Writer renaming (MonadProps to WMProps; _>>F=_ to _>>W=_)
open WFProps
open WAProps
open WMProps
open import Algebra.FunctorProps M renaming (FunctorProps to MFProps; fmap-F to fmap-M)
open import Algebra.ApplicativeProps M renaming (ApplicativeProps to MAProps; pure-F to pure-M; _<*F>_ to _<*M>_)
open import Algebra.MonadProps M renaming (MonadProps to MMProps; _>>F=_ to _>>M=_)
open MFProps
open MAProps
open MMProps
open import Algebra.MonadProps (Writer) renaming (MonadProps to WMProps; _>>F=_ to _>>W=_)

bind-MW-helper : ∀{A B} → (A → M (Writer B)) → Writer A → M (Writer B)
bind-MW-helper f (a , q) = fmap (mul-Writer q) (f a)

bind-MW : ∀{A B} → M (Writer A) → (A → M (Writer B)) → M (Writer B)
bind-MW x f = x >>M= bind-MW-helper f

instance
  writer-monad-composition : Monad (M ∘′ Writer)
  writer-monad-composition = record { _>>=_ = bind-MW }

open import Algebra.ApplicativeProps (M ∘′ Writer) renaming (ApplicativeProps to MWAProps; pure-F to pure-MW; _<*F>_ to _<*MW>_)
open import Algebra.MonadProps (M ∘′ Writer) renaming (MonadProps to MWMProps; _>>F=_ to _>>MW=_)
module Props {{MPM : MMProps}} {{MPQ : MonoidProps}} where
  open MonoidProps MPQ
  open AComp.Props using (applicative-props-composition)
  >>=-assoc-MW : ∀{A B C} (x : M (Writer A)) (f : A → M (Writer B)) (g : B → M (Writer C))
               → (x >>MW= f >>MW= g) ≡ (x >>MW= (λ y → f y >>MW= g))
  >>=-assoc-MW x f g =
    x >>M= bind-MW-helper f >>M= bind-MW-helper g
      ≡⟨ MMProps.>>=-assoc MPM x (bind-MW-helper f) (bind-MW-helper g) ⟩
    (x >>M= λ y → bind-MW-helper f y >>M= bind-MW-helper g)
      ≡⟨ MMProps.>>=-ext MPM x (λ y → bind-MW-helper f y >>M= bind-MW-helper g)
                               (bind-MW-helper (λ y → f y >>MW= g))
                               pf ⟩
    x >>M= bind-MW-helper (λ y → f y >>MW= g)
    ∎
    where pf : ∀ z → (bind-MW-helper f z >>M= bind-MW-helper g) ≡ bind-MW-helper (λ y → f y >>MW= g) z
          pf (a , q) =
            fmap (mul-Writer q) (f a) >>M= bind-MW-helper g
              ≡⟨ MMProps.fmap-bind-simplify MPM (mul-Writer q) (bind-MW-helper g) (f a) ⟩
            f a >>M= bind-MW-helper g ∘′ mul-Writer q
              ≡⟨ >>=-ext MPM (f a) (bind-MW-helper g ∘′ mul-Writer q)
                                           (λ x → bind-MW-helper g x >>M= return ∘′ mul-Writer q)
                                           pf2 ⟩
            f a >>M= (λ x → bind-MW-helper g x >>M= return ∘′ mul-Writer q)
              ≡⟨ >>=-assoc MPM (f a) (bind-MW-helper g) (return ∘′ mul-Writer q) ⟩ʳ
            f a >>M= bind-MW-helper g >>M= return ∘′ mul-Writer q
              ≡⟨ MMProps.return-simplify MPM (mul-Writer q) (f a >>M= bind-MW-helper g) ⟩ʳ
            fmap (mul-Writer q) (f a >>M= bind-MW-helper g)
            ∎
            where pf2 : ∀ z → bind-MW-helper g (mul-Writer q z) ≡ (bind-MW-helper g z >>M= return ∘′ mul-Writer q)
                  pf2 (b , p) =
                    fmap (mul-Writer (q <> p)) (g b)
                      ≡⟨ fmap-ext (fprops (aprops MPM)) (mul-Writer (q <> p)) (mul-Writer q ∘′ mul-Writer p) (mul-Writer-assoc q p) (g b) ⟩
                    fmap (mul-Writer q ∘′ mul-Writer p) (g b)
                      ≡⟨ fmap-comp (fprops (aprops MPM)) (mul-Writer q) (mul-Writer p) (g b)  ⟩
                    fmap (mul-Writer q) (fmap (mul-Writer p) (g b))
                      ≡⟨ MMProps.return-simplify MPM (mul-Writer q) (fmap (mul-Writer p) (g b))  ⟩
                    fmap (mul-Writer p) (g b) >>M= return ∘′ mul-Writer q
                    ∎

  return->>=-right-id-MW : ∀{A} (x : M (Writer A)) → x ≡ (x >>MW= return)
  return->>=-right-id-MW x =
    x
      ≡⟨ return->>=-right-id MPM x ⟩
    (x >>M= return)
      ≡⟨ >>=-ext MPM x return (bind-MW-helper return)
                 (λ { (a , q) → cong (λ e → return (a , e)) (unit-right q) ⟨≡⟩ MMProps.fmap-return MPM (mul-Writer q) (a , mempty)})⟩
    (x >>M= bind-MW-helper return)
    ∎

  return->>=-left-id-MW : ∀{A B} (x : A) (f : A → M (Writer B))
                        → (return x >>MW= f) ≡ f x
  return->>=-left-id-MW a f =
    return (a , mempty) >>M= bind-MW-helper f
      ≡⟨ return->>=-left-id MPM (a , mempty) (bind-MW-helper f) ⟩
    bind-MW-helper f (a , mempty)
      ≡⟨ MFProps.fmap-ext-id (fprops (aprops MPM)) (mul-Writer mempty) (λ { (a′ , p) → cong (_,_ a′) (unit-left p) }) (f a) ⟩ʳ
    f a
    ∎

  >>=-ext-MW : ∀{A B} (x : M (Writer A)) (f g : A → M (Writer B))
             → (∀ a → f a ≡ g a)
             → (x >>= f) ≡ (x >>= g)
  >>=-ext-MW x f g pf = >>=-ext MPM x (bind-MW-helper f) (bind-MW-helper g) λ { (a , q) → cong (fmap (mul-Writer q)) (pf a) }

  <*>-is-ap-MW : ∀{A B} (v : M (Writer (A → B))) (w : M (Writer A))
               → (v <*MW> w) ≡ (v >>MW= λ f → w >>MW= λ x → return (f x))
  <*>-is-ap-MW {A} {B} v w =
    fmap-M ap-W v <*M> w
      ≡⟨ <*>-is-ap MPM (fmap-M ap-W v) w ⟩
    fmap-M ap-W v >>M= (λ f → w >>M= λ x → return (f x))
      ≡⟨ MMProps.fmap-bind-simplify MPM ap-W (λ f → w >>M= λ x → return (f x)) v ⟩
    v >>M= (λ f → w >>M= λ x → return (ap-W f x))
      ≡⟨ >>=-ext MPM v (λ f → w >>M= λ x → return (ap-W f x))
                       (bind-MW-helper (λ f → w >>M= bind-MW-helper (λ x → return (f x))))
                       pf ⟩
    v >>M= bind-MW-helper (λ f → w >>M= bind-MW-helper (λ x → return (f x)))
    ∎
    where pf : ∀ z → (w >>M= (λ x → return (ap-W z x))) ≡ bind-MW-helper (λ f → w >>M= bind-MW-helper (λ x → return (f x))) z as M (Writer B)
          pf (a , q) =
            w >>M= (λ x → return (ap-W (a , q) x))
              ≡⟨ >>=-ext MPM w (λ x → return (ap-W (a , q) x))
                               (λ y → bind-MW-helper (return ∘′ a) y >>M= return ∘′ mul-Writer q)
                               pf2 ⟩
            w >>M= (λ y → bind-MW-helper (return ∘′ a) y >>M= return ∘′ mul-Writer q)
              ≡⟨ >>=-assoc MPM w (bind-MW-helper (return ∘′ a)) (return ∘′ mul-Writer q)  ⟩ʳ
            w >>M= bind-MW-helper (return ∘′ a) >>M= return ∘′ mul-Writer q
              ≡⟨ MMProps.return-simplify MPM (mul-Writer q) (w >>M= bind-MW-helper (return ∘′ a)) ⟩ʳ
            fmap (mul-Writer q) (w >>M= bind-MW-helper (return ∘′ a))
            ∎
            where pf2 : ∀ z → pure-M (ap-W (a , q) z) ≡ (bind-MW-helper (return ∘′ a) z >>M= return ∘′ mul-Writer q)
                  pf2 (b , p) =
                    pure-M (a b , q <> p)
                      ≡⟨ cong (λ e → pure-M (a b , e)) (unit-right (q <> p) ⟨≡⟩ʳ op-assoc q p mempty) ⟩
                    pure-M (a b , q <> p <> mempty)
                      ≡⟨ MAProps.fmap-of-pure (aprops MPM) (mul-Writer q) (a b , p <> mempty) ⟩
                    fmap-M (mul-Writer q) (pure-M (a b , p <> mempty))
                      ≡⟨ cong (fmap (mul-Writer q)) (MAProps.fmap-of-pure (aprops MPM) (mul-Writer p) (a b , mempty)) ⟩
                    fmap-M (mul-Writer q) (fmap (mul-Writer p) (pure-M (a b , mempty)))
                      ≡⟨ MMProps.return-simplify MPM (mul-Writer q) (fmap (mul-Writer p) (return (a b)))  ⟩
                    fmap-M (mul-Writer p) (return (a b)) >>M= return ∘′ mul-Writer q
                    ∎

  writer-monad-props-composition : MWMProps
  writer-monad-props-composition = record
                                     { >>=-assoc = >>=-assoc-MW
                                     ; return->>=-right-id = return->>=-right-id-MW
                                     ; return->>=-left-id = return->>=-left-id-MW
                                     ; >>=-ext = >>=-ext-MW 
                                     ; <*>-is-ap = <*>-is-ap-MW
                                     ; aprops = applicative-props-composition
                                     }
