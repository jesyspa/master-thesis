module MyPrelude where

open import Prelude.Unit public using()
open import Prelude.Empty public using()
open import Prelude.Sum public using()
open import Prelude.Product public using(_×_; _,_)
open import Prelude.Function public using(_∘_; _$_)
open import Prelude.List public using (List; []; _∷_; [_]; map; concatMap)
open import Numeric.Rational public using(Rational; mkratio; _+Q_; _-Q_; _*Q_)

