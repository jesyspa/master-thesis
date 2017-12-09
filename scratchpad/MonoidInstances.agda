module MonoidInstances where

open import MyPrelude
open import Monoid
open import BitProbability
open import ListLemmas

instance
  MonoidList : {A : Set} → Monoid (List A)
  mempty         {{MonoidList}} = []
  _<>_           {{MonoidList}} = _++_
  assoc          {{MonoidList}} = append-assoc-lem
  left-identity  {{MonoidList}} xs = refl
  right-identity {{MonoidList}} xs = right-append-lem

  MonoidProbPlus : Monoid Prob
  mempty         {{MonoidProbPlus}} = never
  _<>_           {{MonoidProbPlus}} = _+P_
  assoc          {{MonoidProbPlus}} = prob-plus-assoc
  left-identity  {{MonoidProbPlus}} = never-left-plus-unit-lem
  right-identity {{MonoidProbPlus}} = never-right-plus-unit-lem

