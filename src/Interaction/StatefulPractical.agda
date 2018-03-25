module Interaction.StatefulPractical where

open import ThesisPrelude
open import Algebra.Proposition

infixr 2 _⊎_
_⊎_ : ∀{l} → Set l → Set l → Set l
_⊎_ = Either

record InteractionStructure : Set₁ where
  field
    State       : Set
    Command     : State → Set
    Response    : {s : State} → Command s → Set
    next        : {s : State}{c : Command s} → Response c → State
open InteractionStructure

record ISMorphism (IS₁ IS₂ : InteractionStructure) : Set where
  field
    StateF    : State IS₁ → State IS₂
    CommandF  : ∀{s} → Command IS₁ s → Command IS₂ (StateF s)
    ResponseF : ∀{s c} → Response IS₂ (CommandF {s} c) → Response IS₁ c
    nextF     : ∀{s c} r → StateF (next IS₁ (ResponseF {s} {c} r)) ≡ next IS₂ r
open ISMorphism

Zero-IS : InteractionStructure
State    Zero-IS = ⊤
Command  Zero-IS s = ⊥
Response Zero-IS ()
next     Zero-IS {c = ()}

id-IS : ∀{IS} → ISMorphism IS IS
StateF    id-IS = id
CommandF  id-IS = id
ResponseF id-IS = id
nextF     id-IS r = refl

comp-IS : ∀{IS₁ IS₂ IS₃} → ISMorphism IS₁ IS₂ → ISMorphism IS₂ IS₃ → ISMorphism IS₁ IS₃
StateF    (comp-IS m₁ m₂) = StateF m₂ ∘′ StateF m₁
CommandF  (comp-IS m₁ m₂) = CommandF m₂ ∘′ CommandF m₁
ResponseF (comp-IS m₁ m₂) = ResponseF m₁ ∘′ ResponseF m₂
nextF     (comp-IS m₁ m₂) r rewrite nextF m₁ (ResponseF m₂ r) | nextF m₂ r = refl 

module _ (IS₁ IS₂ : InteractionStructure) where
  Product-IS : InteractionStructure
  State    Product-IS = State IS₁ × State IS₂
  Command  Product-IS (s₁ , s₂) = Command IS₁ s₁ ⊎ Command IS₂ s₂
  Response Product-IS {s₁ , s₂} (left  c) = Response IS₁ c
  Response Product-IS {s₁ , s₂} (right c) = Response IS₂ c
  next     Product-IS {s₁ , s₂} {left  c} r = next IS₁ r , s₂
  next     Product-IS {s₁ , s₂} {right c} r = s₁ , next IS₂ r

  Incl-L : State IS₂ → ISMorphism IS₁ Product-IS
  StateF    (Incl-L s₂) s₁ = s₁ , s₂
  CommandF  (Incl-L s₂) c = left c
  ResponseF (Incl-L s₂) r = r
  nextF     (Incl-L s₂) r = refl

  Incl-R : State IS₁ → ISMorphism IS₂ Product-IS
  StateF    (Incl-R s₁) s₂ = s₁ , s₂
  CommandF  (Incl-R s₁) c = right c
  ResponseF (Incl-R s₁) r = r
  nextF     (Incl-R s₁) r = refl

data FreeParMonad (IS : InteractionStructure) : State IS → State IS → Set → Set where
  Return-FM : ∀{A s} → A → FreeParMonad IS s s A
  Invoke-FM : ∀{A s s′} → (c : Command IS s) → ((r : Response IS c) → FreeParMonad IS (next IS r) s′ A) → FreeParMonad IS s s′ A

module _ {IS : InteractionStructure} where
  bind-IS : ∀{A B s₁ s₂ s₃} → FreeParMonad IS s₁ s₂ A → (A → FreeParMonad IS s₂ s₃ B) → FreeParMonad IS s₁ s₃ B
  bind-IS (Return-FM a) fun = fun a
  bind-IS (Invoke-FM c cont) fun = Invoke-FM c λ r → bind-IS (cont r) fun

record FMMorphism (IS₁ IS₂ : InteractionStructure) : Set₁ where
  field
    StateM : State IS₁ → State IS₂
    ProgM  : ∀{A s s′} → FreeParMonad IS₁ s s′ A → FreeParMonad IS₂ (StateM s) (StateM s′) A
open FMMorphism

module _ {IS₁ IS₂ : InteractionStructure} (m : ISMorphism IS₁ IS₂) where
  preaction-IS : ∀{A s s′} → FreeParMonad IS₁ s s′ A → FreeParMonad IS₂ (StateF m s) (StateF m s′) A
  preaction-IS (Return-FM a) = Return-FM a
  preaction-IS (Invoke-FM c cont) = Invoke-FM (CommandF m c) lem 
    where
      lem : (r : Response IS₂ (CommandF m c)) → FreeParMonad IS₂ (next IS₂ r) (StateF m _) _
      lem r rewrite sym (nextF m r) = preaction-IS (cont (ResponseF m r))

  action-IS : FMMorphism IS₁ IS₂
  StateM action-IS = StateF m
  ProgM action-IS = preaction-IS

foldr-⊎ : List Set → Set
foldr-⊎ = foldr _⊎_ ⊥

module _ (S : Set) where
  record TySig′ : Set₁ where
    field
      StateFinal : S 
      Arg : Set
      Ret : Set
  TySig : Set₁
  TySig = S → List TySig′

  PlayerSig : Set₁
  PlayerSig = List TySig

open TySig′

module _ {S} where
  MkResponse-impl : (sigs : List (TySig′ S)) → foldr-⊎ (map Arg sigs) → Set
  MkResponse-impl [] ()
  MkResponse-impl (sig ∷ sigs) (left  c) = Ret sig
  MkResponse-impl (sig ∷ sigs) (right c) = MkResponse-impl sigs c

  MkNext-impl : (sigs : List (TySig′ S)) → foldr-⊎ (map Arg sigs) → S
  MkNext-impl [] ()
  MkNext-impl (sig ∷ sigs) (left  c) = StateFinal sig
  MkNext-impl (sig ∷ sigs) (right c) = MkNext-impl sigs c

module _ {S}(IS : InteractionStructure)(sig : TySig S) where
  MkCommand : S → Set
  MkCommand = foldr-⊎ ∘′ map Arg ∘′ sig

  MkResponse : (s : S) → MkCommand s → Set
  MkResponse s c = MkResponse-impl (sig s) c

  MkNext : (s : S) → MkCommand s → S
  MkNext s c = MkNext-impl (sig s) c

  Augment : InteractionStructure
  State    Augment = State IS × S
  Command  Augment (s₁ , s₂) = Command IS s₁ ⊎ MkCommand s₂ 
  Response Augment {s₁ , s₂} (left  c) = Response IS c
  Response Augment {s₁ , s₂} (right c) = MkResponse s₂ c
  next     Augment {s₁ , s₂} {left  c} r = next IS r , s₂
  next     Augment {s₁ , s₂} {right c} _ = s₁ , MkNext s₂ c 

module _ {S}(IS : InteractionStructure)(sigs : PlayerSig S) where
  MkCommand* : S → Set
  MkCommand* s = foldr-⊎ (map (λ sig → foldr-⊎ (map Arg (sig s))) sigs)

  Augment* : InteractionStructure
  State    Augment* = State IS × S
  Command  Augment* (s₁ , s₂) = Command IS s₁ ⊎ MkCommand* s₂ 
  Response Augment* {s₁ , s₂} (left  c) = Response IS c
  Response Augment* {s₁ , s₂} (right c) = {!!}
  next     Augment* {s₁ , s₂} {left  c} r = {!!}
  next     Augment* {s₁ , s₂} {right c} _ = {!!}
  

  
  {-
data Impl (IS : InteractionStructure) : PlayerSig → Set where
  Trivial : Impl IS []
  Method : ∀{arg ret ps} → (arg → FreeMonad IS ret) → Impl IS ps → Impl IS ((arg , ret) ∷ ps)
  -}

{-
fmap-Impl : ∀{IS₁ IS₂ : InteractionStructure}(ps : PlayerSig) → ISMorphism IS₁ IS₂ → Impl IS₁ ps → Impl IS₂ ps
fmap-Impl [] m Trivial = Trivial
fmap-Impl ((_ , _) ∷ ps) m (Method f impl) = Method (λ a → action-IS m (f a)) (fmap-Impl ps m impl)
-}


{-
Augment : InteractionStructure → TySig → InteractionStructure
State    (Augment IS (arg , ret)) = State IS
Command  (Augment IS (arg , ret)) s = {!!}
Response (Augment IS (arg , ret)) (left  c) = {!!}
Response (Augment IS (arg , ret)) (right c) = {!!}
next     (Augment IS (arg , ret)) = {!!}
-}

{-
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

-}
