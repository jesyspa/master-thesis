module Interaction.Practical where

open import ThesisPrelude
open import Algebra.Proposition

record InteractionStructure : Set₁ where
  field
    Command     : Set
    Response    : Command → Set
open InteractionStructure

record ISMorphism (IS₁ IS₂ : InteractionStructure) : Set where
  field
    CommandF  : Command IS₁ → Command IS₂
    ResponseF : ∀{c} → Response IS₂ (CommandF c) → Response IS₁ c
open ISMorphism

Zero-IS : InteractionStructure
Command  Zero-IS = ⊥
Response Zero-IS ()

id-IS : ∀{IS} → ISMorphism IS IS
CommandF  id-IS = id
ResponseF id-IS = id

comp-IS : ∀{IS₁ IS₂ IS₃} → ISMorphism IS₁ IS₂ → ISMorphism IS₂ IS₃ → ISMorphism IS₁ IS₃
CommandF  (comp-IS m₁ m₂) = CommandF m₂ ∘′ CommandF m₁
ResponseF (comp-IS m₁ m₂) = ResponseF m₁ ∘′ ResponseF m₂

infixr 2 _⊎_
_⊎_ : ∀{l} → Set l → Set l → Set l
_⊎_ = Either

module _ (IS₁ IS₂ : InteractionStructure) where
  Product-IS : InteractionStructure
  Command  Product-IS = Command IS₁ ⊎ Command IS₂
  Response Product-IS (left  c) = Response IS₁ c
  Response Product-IS (right c) = Response IS₂ c

  Incl-L : ISMorphism IS₁ Product-IS
  CommandF  Incl-L = left
  ResponseF Incl-L = id

  Incl-R : ISMorphism IS₂ Product-IS
  CommandF  Incl-R = right
  ResponseF Incl-R = id

data FreeMonad (IS : InteractionStructure) : Set → Set where
  Return-FM : ∀{A} → A → FreeMonad IS A
  Invoke-FM : ∀{A} → (c : Command IS) → (Response IS c → FreeMonad IS A) → FreeMonad IS A

module _ {IS : InteractionStructure} where
  bind-IS : ∀{A B} → FreeMonad IS A → (A → FreeMonad IS B) → FreeMonad IS B
  bind-IS (Return-FM a) fun = fun a
  bind-IS (Invoke-FM c cont) fun = Invoke-FM c λ r → bind-IS (cont r) fun

FMMorphism : (IS₁ IS₂ : InteractionStructure) → Set₁
FMMorphism IS₁ IS₂ = ∀{A} → FreeMonad IS₁ A → FreeMonad IS₂ A

action-IS : {IS₁ IS₂ : InteractionStructure} → ISMorphism IS₁ IS₂ → FMMorphism IS₁ IS₂
action-IS m (Return-FM a) = Return-FM a
action-IS m (Invoke-FM c cont) = Invoke-FM (CommandF m c) λ r → action-IS m (cont (ResponseF m r))

TySig : Set₁
TySig = Set × Set

argT : TySig → Set
argT = fst
retT : TySig → Set
retT = snd

PlayerSig : Set₁
PlayerSig = List TySig

MkCommand : PlayerSig → Set
MkCommand [] = ⊥
MkCommand ((arg , ret) ∷ ps) = arg ⊎ MkCommand ps

MkResponse : (ps : PlayerSig) → MkCommand ps → Set 
MkResponse [] ()
MkResponse ((arg , ret) ∷ ps) (left  c) = ret
MkResponse ((arg , ret) ∷ ps) (right c) = MkResponse ps c

Augment : InteractionStructure → TySig → InteractionStructure
Command  (Augment IS (arg , ret)) = Command IS ⊎ arg
Response (Augment IS (arg , ret)) (left  c) = Response IS c
Response (Augment IS (arg , ret)) (right c) = ret

Augment* : InteractionStructure → PlayerSig → InteractionStructure
Command  (Augment* IS ps) = Command IS ⊎ MkCommand ps 
Response (Augment* IS ps) (left  c) = Response IS c
Response (Augment* IS ps) (right c) = MkResponse ps c

Augment** : InteractionStructure → List PlayerSig → InteractionStructure
Augment** IS [] = IS
Augment** IS (ps ∷ pss) = Augment* (Augment** IS pss) ps

embed-Augment* : (IS : InteractionStructure)(ps : PlayerSig) → ISMorphism IS (Augment* IS ps)
CommandF  (embed-Augment* IS ps) = left
ResponseF (embed-Augment* IS ps) = id

fmap-Augment* : ∀{IS₁ IS₂ : InteractionStructure}(ps : PlayerSig) → ISMorphism IS₁ IS₂ → ISMorphism (Augment* IS₁ ps) (Augment* IS₂ ps)
CommandF  (fmap-Augment* ps m) (left  c) = left (CommandF m c)
CommandF  (fmap-Augment* ps m) (right c) = right c
ResponseF (fmap-Augment* ps m) {left  c} r = ResponseF m r
ResponseF (fmap-Augment* ps m) {right c} r = r

embed-Augment** : (IS : InteractionStructure)(pss : List PlayerSig) → ISMorphism IS (Augment** IS pss)
embed-Augment** IS [] = id-IS
embed-Augment** IS (ps ∷ pss) = comp-IS (embed-Augment* IS ps) (fmap-Augment* ps (embed-Augment** IS pss))

embed-Command-Augment* : (IS : InteractionStructure)(ps : PlayerSig) → Command IS → Command (Augment* IS ps) 
embed-Command-Augment* IS ps = left

embed-Command-Augment** : (IS : InteractionStructure)(pss : List PlayerSig) → Command IS → Command (Augment** IS pss)
embed-Command-Augment** IS [] = id
embed-Command-Augment** IS (ps ∷ pss) = embed-Command-Augment* (Augment** IS pss) ps ∘′ embed-Command-Augment** IS pss

module _ (IS₁ IS₂ : InteractionStructure) where
  embed-Interchange : (pss : List PlayerSig) → Command (Augment** IS₁ pss) → Command (Augment** (Product-IS IS₁ IS₂) pss)
  embed-Interchange [] c = left c
  embed-Interchange (ps ∷ pss) (left  c) = left (embed-Interchange pss c)
  embed-Interchange (ps ∷ pss) (right c) = right c
  
  undo-embed-Interchange : (pss : List PlayerSig)(c : Command (Augment** IS₁ pss))
                         → Response (Augment** (Product-IS IS₁ IS₂) pss) (embed-Interchange pss c)
                         → Response (Augment** IS₁ pss) c
  undo-embed-Interchange [] c r = r
  undo-embed-Interchange (ps ∷ pss) (left  c) r = undo-embed-Interchange pss c r
  undo-embed-Interchange (ps ∷ pss) (right c) r = r

data Impl (IS : InteractionStructure) : PlayerSig → Set where
  Trivial : Impl IS []
  Method : ∀{arg ret ps} → (arg → FreeMonad IS ret) → Impl IS ps → Impl IS ((arg , ret) ∷ ps)

fmap-Impl : ∀{IS₁ IS₂ : InteractionStructure}(ps : PlayerSig) → ISMorphism IS₁ IS₂ → Impl IS₁ ps → Impl IS₂ ps
fmap-Impl [] m Trivial = Trivial
fmap-Impl ((_ , _) ∷ ps) m (Method f impl) = Method (λ a → action-IS m (f a)) (fmap-Impl ps m impl)

module _ (IS₁ IS₂ : InteractionStructure) where
  resolve : ∀{A}(sig : TySig) → FreeMonad (Augment IS₁ sig) A → (argT sig → FreeMonad IS₂ (retT sig)) → FreeMonad (Product-IS IS₁ IS₂) A
  resolve (arg , ret) (Return-FM a) fun = Return-FM a
  resolve (arg , ret) (Invoke-FM (left  c) cont) fun = Invoke-FM (left c) λ r → resolve (arg , ret) (cont r) fun
  resolve (arg , ret) (Invoke-FM (right c) cont) fun = bind-IS (action-IS (Incl-R IS₁ IS₂) (fun c)) λ r → resolve (arg , ret) (cont r) fun 

  resolve-impl : (ps : PlayerSig)(c : MkCommand ps) → Impl IS₂ ps → FreeMonad IS₂ (MkResponse ps c)
  resolve-impl [] () _
  resolve-impl ((arg , ret) ∷ ps) (left  c) (Method m impl) = m c
  resolve-impl ((arg , ret) ∷ ps) (right c) (Method m impl) = resolve-impl ps c impl

  module _ {ps : PlayerSig} where
    resolve* : ∀{A} → FreeMonad (Augment* IS₁ ps) A → Impl IS₂ ps → FreeMonad (Product-IS IS₁ IS₂) A
    resolve* (Return-FM a) impl = Return-FM a
    resolve* (Invoke-FM (left  c) cont) impl = Invoke-FM (left c) λ r → resolve* (cont r) impl
    resolve* (Invoke-FM (right c) cont) impl = bind-IS (action-IS (Incl-R IS₁ IS₂) (resolve-impl ps c impl)) λ r → resolve* (cont r) impl

  resolve** : (ps₁ ps₂ : PlayerSig) → Impl (Augment* IS₁ ps₂) ps₁ → Impl IS₂ ps₂ → Impl (Product-IS IS₁ IS₂) (ps₁ ++ ps₂)
  resolve** [] ps₂ Trivial impl₂ = fmap-Impl ps₂ (Incl-R IS₁ IS₂) impl₂
  resolve** ((_ , _) ∷ ps₁) ps₂ (Method f impl₁) impl₂ = Method (λ a → resolve* (f a) impl₂) (resolve** ps₁ ps₂ impl₁ impl₂)

  module _ (ps : PlayerSig)(pss : List PlayerSig) where
    resolve*1 : ∀{A}
              → FreeMonad (Augment** IS₁ (ps ∷ pss)) A → Impl IS₂ ps
              → FreeMonad (Augment** (Product-IS IS₁ IS₂) pss) A
    resolve*1 (Return-FM a) impl = Return-FM a
    resolve*1 (Invoke-FM (left  c) cont) impl
      = Invoke-FM (embed-Interchange IS₁ IS₂ pss c)
                  λ r → resolve*1  (cont (undo-embed-Interchange IS₁ IS₂ pss c r)) impl
    resolve*1 (Invoke-FM (right c) cont) impl
      = bind-IS (action-IS (comp-IS (Incl-R IS₁ IS₂) (embed-Augment** (Product-IS IS₁ IS₂) pss)) (resolve-impl ps c impl))
                λ r → resolve*1 (cont r) impl 


data Impl* : List InteractionStructure → List PlayerSig → Set₁ where
  Nil-Impl*  : Impl* [] [] 
  Cons-Impl* : ∀{ps pss IS ISs} → Impl (Augment* IS (concat pss)) ps → Impl* ISs pss → Impl* (IS ∷ ISs) (ps ∷ pss)

Product-IS* : List InteractionStructure → InteractionStructure
Product-IS* [] = Zero-IS
Product-IS* (IS ∷ ISs) = Product-IS IS (Product-IS* ISs)

resolve*** : (ISs : List InteractionStructure)(pss : List PlayerSig) → Impl* ISs pss → Impl (Product-IS* ISs) (concat pss)
resolve*** [] [] Nil-Impl* = Trivial
resolve*** (IS ∷ ISs) (ps ∷ pss) (Cons-Impl* impl impls) = resolve** IS (Product-IS* ISs) ps (concat pss) impl (resolve*** ISs pss impls)

