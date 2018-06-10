module Algebra.Fibered.FunctorMorphismCat where

open import ThesisPrelude
open import Algebra.Fibered.FiberedSet
open import Algebra.Fibered.Functor
open import Algebra.Fibered.FunctorMorphism

open FiberedFunctorMorphism

module _ {I}{F : FiberedSet I → FiberedSet I}{{FF : FiberedFunctor F}} where
  open FiberedFunctor FF
  id-FFM : FiberedFunctorMorphism id F F
  RunFFM id-FFM s = fmapᶠ s

module _ {I J K}{ri : I → J}{rj : J → K}
         {F : FiberedSet I → FiberedSet I}{{FF : FiberedFunctor F}}
         {G : FiberedSet J → FiberedSet J}{{FG : FiberedFunctor F}}
         {H : FiberedSet K → FiberedSet K}{{FH : FiberedFunctor F}} where
  open FiberedFunctor {{...}}
  comp-FFM : FiberedFunctorMorphism ri F G
           → FiberedFunctorMorphism rj G H
           → FiberedFunctorMorphism (rj ∘′ ri) F H
  RunFFM (comp-FFM ff fg) {X} {Y} ra
    = comp-RA {X = F X} {Y = G (reindex ri X)} {Z = H Y} (RunFFM ff (embed-reindexed ri {X})) (RunFFM fg (colift-reindexed ri rj {X} ra))
    -- Okay, admittedly, this isn't much better than the Kan extension approach.
