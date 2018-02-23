module Utility.Identity where

open import ThesisPrelude

Identity : ∀{l} → Set l → Set l
Identity = id

instance
  FunctorIdentity : ∀{l} → Functor (Identity {l})
  FunctorIdentity = record { fmap = id }

  ApplicativeIdentity : ∀{l} → Applicative (Identity {l})
  ApplicativeIdentity = record { pure = id ; _<*>_ = id }

  MonadIdentity : ∀{l} → Monad (Identity {l})
  MonadIdentity = record { _>>=_ = flip _$′_ }

