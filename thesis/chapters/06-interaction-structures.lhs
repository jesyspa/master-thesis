\chapter{Interaction Structures}

In previous chapters, we have expressed both challenger and adversary in the
same basic instruction set, and then expressed the oracle separately (since it
required instructions we could not afford to allow to the adversary).  This was
not ideal: the challenger had access to instructions that are only for the
adversary's use, and the difference in the way the adversary and oracle were
specified made it harder to reason about indistinguishability.

The problem arises from requiring that every player be expressed in terms of the
same instruction set.  However, defining a new instruction set for every player
duplicates a lot of code: the functor and monad instances have to be replicated,
as well as the evaluation function.  We thus want a way of generating a monad
like |CryptoExpr| given a set of instructions that it must support.

We achieve this by defining a category of interaction structures and then a
functor from that into the category of indexed morphisms.  Now that I think
about it, I'm pretty sure there should be some kind of functor in the other
direction that's right adjoint to this functor.  This is totally useless but
fun.

\section{Definition}

An interaction structure is a set of states, set of commands per state, set of
responses per command, and a next state for every response.  An interaction
structure morphism sends states to states and commands to commands covariantly,
responses to responses contravariantly, and commutes with the next state map.

\begin{code}
record InteractionStructure (S : Set) : Set where
  field
    Command   : S -> Set
    Response  : {s : S} -> Command s -> Set
    next      : {s : S}(c : Command s)(r : Response c) -> S

record ISMorphism {S1 S2 : Set}
                  (IS1 : IntStruct S1)(IS2 : IntStruct S2)
                  (StateF : S1 -> S2) : Set where
  field
    CommandF   : {s : S1} -> Command IS1 s -> Command IS2 (StateF s)
    ResponseF  : {s : S1}{c : Command IS1 s}
               -> Response IS2 (CommandF c) -> Response IS1 c
    nextF      : {s : S1}(c : Command IS1 s)(r : Response IS2 (CommandF c))
               -> StateF (next IS1 c (ResponseF r)) == next IS2 (CommandF c) r
\end{code}

\section{Constructions}

There is a tensor product operation definable on the category of interaction
structures.  This represents a two-player system with each instruction modifying
one player state.

TODO: Show code.

When players may depend on each other, the above construction is too permissive.
A possible action player A may take is calling a method of player B, which may
change player B's state.  We thus want player A's state to include a model of
player B's state.  Moreover, player B may perform an action independent of
player A, which should still be representable in player A's state.  Hence,
player A's state must be a product of his internal state and B's state.

(I suspect a certain amount of reindexing may be possible to allow for the state
to be smaller; in this case, player A `forgets' some of the details of player
B's state (or determines some of his own state based on that of player B).  It
hasn't shown up in code yet, though.)

\section{Free Monads}

Given an interaction structure we can find a free monad on it.  This is
basically exactly what we wanted.

Apart from this, it gives us a notion of simulation for interaction structures,
which again gives rise to a category by Kleisli composition.

