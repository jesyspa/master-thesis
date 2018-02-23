module Utility.Identity where

import ThesisPrelude

Identity : ∀{l} → Set l → Set l
Identity = id

-- postulate monadicity
