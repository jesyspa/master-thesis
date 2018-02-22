\chapter{Games in Agda}

In this chapter, we will look at how games can be represented as formal objects in Agda, and then interpret these
objects with the help of the distribution monad from the previous chapter.

This chapter is split into three sections, the first describing the interface that is supported, the second
showing how this can be implemented in Agda, and the third showing that there exists a valuation function on this
syntax.

\section{Interface}

We start by specifying a datatype that describes the computations we would like to work with; this is the |Game| type
from the introduction.  In this context, we want to specialise |Game| to only refer to complete games, and instead use
|CryptoExpr| for game fragments.

As before, we would like to parametrise |CryptoExpr| by the type of the result, as well as the state of the adversary.
However, rather than making the adversary choose a single state type to work with for the duration of the game, we allow
for the state type to vary, and track an initial and final adversary state type.  |CryptoExpr| thus takes three
parameters of type |Set|: an initial adversary state, a final adversary state, and a result type.

A |Game| is a |CryptoExpr| where the initial and final adversary state types are both restricted to the unit type.  This
conveniently trivialises both the choice of initial adversary state and makes the final distribution depend exclusively
on the result, since the state has a unique inhabitant.

We occasionally remark that |CryptoExpr| must satisfy certain equations.  In practice, it may be more convenient to
require that only the interpretations of these terms satisfy these equations.  In the final thesis, we will be explicit
about where we require which.

\subsection{Randomness Operations}

The fundamental operation that gives access to random bits is
\begin{code}
    uniform-expr : forall{S} (n : Nat) -> CryptoExpr S S (BitVec n)
\end{code}
This gives a uniform distribution over bit vectors of the given length.  We use the |expr| suffix on these functions to
indicate that they are purely syntactic constructs; in the next chapter, they will be interpreted as the corresponding
values without the suffix.

A derived operation of |uniform-expr| is |coin-expr : \forall{S} -> CryptoExpr S S Bool|, which represents a single
fair coin flip.  While very useful in practice, it is not significantly different to |uniform-expr 1| and we will thus
not treat it separately in most cases.

\subsection{Adversary Operations}

In addition to generating random bits, the adversary may set and get the state.  As before, this involves two operations
\begin{code}
    get-adv-state-expr : forall{S} -> CryptoExpr S S S
    put-adv-state-expr : forall{S S'} -> S' -> CryptoExpr S S' ()
\end{code}

It is necessary to provide these operations to allow for the construction of stateful adversaries, but they are never
used explicitly in a proof of security: an arbitrary adversary is taken, while the game and encryption scheme cannot use
these operations.

These operations should satisfy the usual laws of the state monad: getting a value and putting it back is a no-op,
putting a value and immediately getting it yields the value, putting two values is the same as putting the latter, and
getting a value twice gives the same value.

\subsection{General Operations}

In addition to these domain-specific operations, |CryptoExpr| is a monad in its third parameter, with the restriction
that it should act as an arrow in the first and second parameters, in the sense that it must support the following
operations:
\begin{code}
    return-expr : forall{S A} -> A -> CryptoExpr S S A
    bind-expr : forall{S S' S'' A B} -> CryptoExpr S S' A
              -> (A -> CryptoExpr S' S'' B)
              -> CryptoExpr S S'' B
\end{code}

This is a special case of an indexed monad~\cite{indexedmonads}.  A formalisation of this notion and an interpretation
of it in category theory would be a fun digression, if time permits.

These operations should satisfy both the laws of a monad (when the arrow structure permits composition) and of an arrow.
We will specify the precise laws that must be satisfied in the final thesis.  In the construction we have currently
found, functional extensionality is required to satisfy these laws on the nose.

\subsection{Security Constraints}

In addition to the syntax of the games, we must also define the syntax of the conditions we may pose upon the games.
The only condition we can express at the moment is equality of games, denoted |==G|.  We assume that the adversary
states are both initially and finally |top|.

There is a design choice here: we can make |==G| a purely syntactic construct with type |Game A -> Game A -> GameEq A|
which can then later be interpreted as a proposition once a valuation is chosen.  On the other hand, we can skip this
intermediate step and parametrise |==G| by the chosen valuation.  It is yet unclear which option is preferrable, though
the latter appears more useful at the moment.

Since most intermediate steps involve showing that a particular part of the games is equivalent, we need a similar
notion for arbitrary elements of |CryptoExpr S S' A|.  This is straightforward from a syntactic point of view, though it
has considerable semantic consequences.

Similarly, we can generalise this syntactic notion of equivalence to an equivalence-up-to-$\epsilon$ simply by
introducing an extra parameter $\epsilon$.  More complicated forms, such as parametrised or asymptotic security, are
simply a matter of making $\epsilon$ a function of some security parameter, which does not require any extra machinery
on our part.

\section{Implementation}

In order to express the above syntax, we use a free monad construction in a continuation-passing style.  There is a
|Return : A -> CryptoExpr S S A| constructor.  An operation of the form |op : \Gamma -> CryptoExpr S S' A| is
implemented as a constructor |Op : \Gamma -> (A -> CryptoExpr S' S'' B) -> CryptoExpr S S'' B|.  We then define
\begin{code}
    op \gamma = Op \gamma Return
\end{code}

Bind is defined operation.  Given an |Op \gamma cont| (as above) and a function |f : B -> CryptoExpr S'' S'''|, the
bind is |Op \gamma (bind cont f)|; bind of |Return b| is |f b|.

It is easy to verify that assuming functional extensionality, this satisfies the usual monad laws, restricted to
matching adversary states.  We expect this construction to be sufficient for implementing all syntactic operations of
|CryptoExpr|.  A possible design choice is to provide a |Bind| constructor, though it is unclear why this would be
beneficial.

The interpretation of equivalence on |CryptoExpr| terms depends on the approach taken: if we let these equality be
constructs be purely syntactic, then the equality (and inequality) operators simply pair their arguments for later
interpretation.  If the interpretation is direct, then more work is required, and we defer the discussion of that to the
following chapter.

\section{Valuation}

(WIP)

We will now show that games really do denote non-deterministic computations with a stateful adversary by implementing a
function that sends a |CryptoExpr S S' X| to an indexed state monad transformer over a probability distribution monad.

The individual randomness operations are straightforward to implement (lifts of probability operations), as are the
adversary's state modification operations (operations of the state monad).  The strict equivalence notion is also no
problem, since (assuming that the result type |A| has decidable equality) we can require that sampling every element of
|A| gives equivalent results under both distributions.

The equivalent-up-to-$\epsilon$ notion gives more freedom in interpretation.  The choice that seems best at the moment
is to say that the valuations of expressions |E1| and |E2| are equivalent up to $\epsilon$ iff for every initial
adversary state, the maximum absolute difference in sampling probability between the two valuations is at most
$\epsilon$.  The alternative is to require that the sum of the absolute differences of every sample is bounded by
$\epsilon$.  However, this requires a finiteness assumption (or a measure) on the final state of the adversary and on
the result type, which may not be desirable.

The motivation for one choice over the other shall come from what results can be proven about congruences involving this
notion of inequality; if we replace a portion of a game with a portion that differs by at most $\epsilon$, what can we
say about the game as a whole?  This is another important research question we aim to address.

