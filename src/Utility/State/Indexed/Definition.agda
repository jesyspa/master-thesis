module Utility.State.Indexed.Definition where

open import ThesisPrelude
open import Algebra.Lift
open import Algebra.Indexed.Monad

-- There exists an indexed state monad.  However, since the identity has the wrong
-- signature (mismatch of universes), we have to use Lift, which isn't a Monad in
-- the agda-prelude sense of the word (it is universe-polymorphic).  This means we
-- cannot reuse the LiftM machinery, so it's too much trouble to bother with right
-- now.
