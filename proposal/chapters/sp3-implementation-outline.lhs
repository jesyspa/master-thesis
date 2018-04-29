\section{Design Outline}
\label{sec:work}

We will now briefly present the design that we have developed so far.  This development is sufficient to represent games
featuring only a challenger and an adversary, compute the probability of an adversary winning the game, and reason about
two games having equal victory probability for the adversary.  These features suffice to represent the proof of the
One-Time Pad being secure against eavesdropping (as presented in \ref{sec:example}), though they are not enough to prove
that the One-Time Pad is not vulnerable against a chosen plaintext attack.

% What issues are still unresolved?
% - Different notions of security: bounded by a constant, asymptotic, etc.
% - Oracles
% - Bounds on computation
% - Proof automation
% What do we need to introduce for this?
% - A syntactic monad that represents the computations.
% - A valuation for this monad.  Perhaps just note that this valuation requires us to be able to reason about
%   equalities?
% - A notion of equality of valuations.
% Other thoughts:
% - I could scrap the whole OTP example.  I suppose it's an interesting tidbit but not very useful (?)
% - 

\subsection{Agda as a Proof Assistant}

We assume that the reader is already familiar with the Agda programming language\todo{Add a link to a tutorial?} and
with the propositions-as-type approach of encoding proofs.  Briefly, when using this approach we represent a proposition
by a type, the terms of which are proofs of this proposition.  We say a proposition represented by a type |T| is true if
we can construct a term |t : T|.  We say a proposition is false if we can construct a term |nt : T ->
bot|.\todo{Definitely reference a tutorial.}

When introducing game-playing proofs, we used Haskell to represent our games.  A similar construction can be used to
encode our games in Agda, with the added benefit that we can use the same language to represent properties of games and
relations between games, and to prove that these properties and relations hold.\todo{Something about advantages?}

\todo{Something about why Agda?}

Since our primary focus lies on the representation of games and reasoning about their valuations as probability
distributions, we will not perform the underlying constructions like lists and natural numbers ourselves, instead
relying on Ulf Norell's \texttt{agda-prelude}\footnote{\url{https://github.com/UlfNorell/agda-prelude}} library for
these.  Furthermore, we assume the existence of a type representing probabilities; for example, the rational numbers
satisfy all the properties that we will require of this type.

\subsection{Games}

From the point of view of our implementation, a game is a syntactic description of a stateful, non-deterministic
computation.  We can represent this using a free monad over the collection of operations that are supported.  Games can
be parametrised over an encryption scheme and adversary, both of which are also computations in this free monad.

In order to reason about games, we need to give them semantics.  The key difficulty is the representation of probability
distributions.  Fortunately, there is prior work on the matter both for finite~\cite{probfunproghaskell} and infinite

\subsection{Valuations}

% Valuations are what we map games into.
% Essential properties: we can compute the probability of some outcome.

\subsection{Representation of Distributions}

There is considerable prior work done on formalising probability distributions in a functional setting in the
past.\todo{cite relevant stuff}  For our purposes, the primary interest lies in probability distributions with finite
support.  The most fitting representation for a distribution in this setting is a list of pairs, each pair containing an
outcome and its probability.  Duplicates are allowed, in which case the probability of the outcome is the sum of the
probabilities it is paired with.

In other words, given a type |A| we construct a type |ListDist A| isomorphic to |List (A * Q)|.  This is easily seen to
be the |Writer| monad transformer applied to the |List| monad, with multiplication on |Q| as the monoidal operation.
The monadic structure expresses the following: given a distribution |D : ListDist A| and a family of distributions |f :
A -> ListDist B|, the combined distribution |D >>= f| represents picking an |a : A| according to |D| and then a |b : B|
according to |f a|.

The monadic structure also gives rise to a way of constructing distributions: given |a : A|, |return a : ListDist A| is
the distribution that always yields |a|.  We also require that the uniform distribution over bitstrings of length |n|
exist for every |n : Nat|; that is, we require a function |uniform : (n : Nat) -> ListDist (BitVec n)| which gives
probability |negpow2 n| to each outcome.

%{
%format D1 = "D_1"
%format D2 = "D_2"
Finally, we require that if the type |A| has decidable equality, then we can compute the probability of sampling an |a :
A| from a |D : ListDist A|; that is, that there exists a function |sample : {{Eq A}} -> ListDist A -> A -> Q|.  This
gives rise to a notion of indistinguishibility of distributions |==D|, where |D1 ==D D2| is a type that is inhabited iff
for every |a : A|, |sample D1 a == sample D2 a|.  We will generally be interested in distributions up to this
equivalence relation.
%}

Although this implementation of distribution seems to be the most practical for our purposes, we parametrise the
remainder of the construction by the implementation used, allowing a different implementation to be specified if
desired.

\subsection{Representation of Games}

A game represents a non-deterministic computation.  While we could represent a game directly in the |ListDist| monad,
this would make it harder to argue about properties of the adversary.  Instead, we provide a monad in which games and
adversaries can be described syntactically and provide a valuation function from this monad into the distribution monad.

This syntactic monad is the free monad over the signature of operations that players have access to.  Due to the limited
scope of what has been implemented so far, this is only the |uniform| operation that takes an |n : Nat| and returns a
|BitVec n| uniformly at random.

\todo{Say something more?}
