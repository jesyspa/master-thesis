\section{Implementation Outline}
\label{sec:work}

% Briefly: what do we want here?
% What approaches we've already taken and have proven successful.
% These are: probabilities as rational numbers, distributions using lists, sample equality as equivalence.
% distributions as monads!

In this chapter, we will give a high-level overview of the appoaches we have already found to be successful.  The goal
is to show that the problem we have set out to solve is reasonably solvable.

\subsection{Preliminary Setup}

We assume that the reader is already familiar with the Agda programming language.\todo{Add a link to a tutorial?}

Our focus in this project is on the representation of and reasoning with probability distributions and randomised
computations.  As such, we use existing libraries for basic type constructions like sums, products, lists, and natural
numbers, as well as for common typeclasses such as functor and monad.  In our implementation, we use Ulf Norell's
\texttt{agda-prelude} library for this.

Additionally, we have for now assumed the existence of a type |Q| suitable for representing probabilities.  It is
convenient from a programming perspective to not require such a type to contain values exclusively in the $[0, 1]$
interval; though this would make it easier to quantify over an arbitrary probability, it would mean the type is not
closed under addition or subtraction, making it considerably harder to express the operations we care about.  As such,
we require that this type be an ordered ring of characteristic zero with an additional |negpow2 : Nat -> Q| operation
that maps $n$ to the multiplicative inverse of $2^n$.  Since the rationals constructively satisfy these properties and
are thus a valid implementation of this type, we consider postulating the existince of an implementation to be
unproblematic.

A consequence of this choice of requirements on $Q$ is that a formalisation of the real numbers does \emph{not} a valid
implementation, as they lack a decidable total order.  We have as of yet not made sufficient use of the order on $Q$ to
determine whether this is a correctable issue.  However, given the nature of our problem it seems unlikely that
non-rational probabilities are of interest, and so we consider this not to be a significant handicap.

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
