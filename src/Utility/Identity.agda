module Utility.Identity {l} where

open import ThesisPrelude

Identity : Set l → Set l
Identity = id

instance
  FunctorIdentity : Functor Identity
  FunctorIdentity = record { fmap = id }

  ApplicativeIdentity : Applicative Identity
  ApplicativeIdentity = record { pure = id ; _<*>_ = id }

  MonadIdentity : Monad Identity
  MonadIdentity = record { _>>=_ = flip _$′_ }

