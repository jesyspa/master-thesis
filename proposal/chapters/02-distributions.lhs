\chapter{Probability in Agda}

In this chapter, we discuss how we can use Agda to represent the probability distributions that our games ultimately
stand for.  The goal is to obtain a type |Q| of probabilities and a type constructor |D| that sends a type |A| to the
type of probability distributions over |A| and establish the properties that these must have to be useable in providing
valuations for games.

For greater generality, we use Agda's |record| feature to split the interface that we require |Q| and |D| to have from
the implementation.  We do not currently have an example of |Q| implemented, but all the properties we require hold in
the rational numbers, which are representable in Agda.  For |D| we provide an outline for to approaches to its
implementation.


\section{Probability}

In order to discuss how probability distributions can be sampled, we will need a type for representing probability
values.  A key question we must ask ourselves is whether this type should \emph{only} be able to represent values in the
$[0, 1]$ interval, or whether values that are not probabilities should also be representable.

We have chosen to go for the later options.  It is very convenient for probabilities to be a group under addition, which
the interval $[0, 1]$ is not.  While an implementation that distinguishes the types of probabilities, differences
between probabilities, and sums of probabilities would be an interesting project in itself, it would add little to the
logic we are studying.

Instead, we require that the type of probabilities |Q| be an ordered ring with negative powers of two, in the sense that
there is a function |negpow2 : Nat -> Q| such |negpow2 0 == 1| and |times 2 (negpow2 ((plus n 1))) == negpow2 n|.\footnote{Where by 0
and 1 we mean the corresponding values in the ring structure, and |2 == (plus 1 1)|.}  This suffices to implement
probabilities that occur when the only source of randomness are uniform distributions over sets with size a power of
two.  If we wish to add a |Repeat| combinator, as discussed in the previous chapter, then requiring that |Q| be an
ordered field will be necessary.

We have so far not implemented this type, but given that the rationals satisfy all these assumptions in a constructive
manner, we believe that it should have an implementation.

Note that since an ordered ring necessarily has a \emph{total} order, the real numbers are \emph{not} a model of
probability, since real equality is not constructively decidable.  We have yet to see whether we will ever make use of
this decidability.  In any case, it is unclear that using the real numbers as |Q| would have any advantages, since all
probabilities we arrive at are by construction rational.

Having posed these requirements, we allow the user of our code to specify their preferred type that satisfies these
properties, by the means of implementing a record.  This corresponds to defining a |Probability| typeclass in Haskell.

\section{Distributions: Abstract Specification}

We now assume that we have a specific type |Q| of probabilities and build a notion of distributions on top of it.
A distribution is a type |D A| parametrised over the type |A| of values that the distribution takes.

A distribution is a monad with support for sampling |sample : {{_ : Eq A}} -> D A -> A -> Q| and generating a uniform
distribution |uniform : (n : Nat) -> D (BitVec n)|, such that |sample (uniform n) v == negpow2 n| for any |v : BitVec
n|.

The sampling function gives rise to a notion of equivalence between distributions.  We say distributions |D1| and |D2|
over a type |A| with decidable equality are sample-equivalent if for every element |a : A|, |sample D1 a == sample
D2 a|.  The monadic bind should preserve equivalences on both sides.  Furthermore, interchange of the sequencing order
should give equivalent distributions if the second distribution does not depend on the first.

The uniform distribution is equivalent to itself under the image of any bijection, and if |f : A -> B| is injective,
then |sample D a == sample (fmap f D0) (f a)| for any |D0 : D A| and |a : A|.  Furthermore, any distribution |D0 : D A|
is equivalent to itself sequenced after the uniform distribution (i.e., |uniform n >>= const D0|).  The reason we
require this to hold specifically for the uniform distribution, rather than simply any distribution, is that we do not
assume that an arbitrary distribution has probabilities summing to one.  However, since we are only interested in
distributions which arise by applying the valuation function to a |CryptoExpr| term, this is not a problem.  (The
distributions produced by |return| sum to one by the monad laws.)

For technical reasons, instead of representing the probability as a paremeter to the typeclass |DistMonad|, we make |Q|
a field of the typeclass record.  This way, instead of parametrising over an arbitrary type of probabilities and then
over an arbitrary distribution type using those probabilities, we can directly parametrise over an arbitrary
distribution type and get the type of probabilities automatically.

We do not require that given a distribution, we can retrieve its support.  This simply does not seem to be relevant to
any of the proofs we wish to do.

\section{List-Based Distributions}

We have been able to construct a model of the above specification using a Writer (with type |Q| under multiplication)
monad transformer over a list monad.  The uniform distribution is implemented as the list of all possible bitstrings of
length |n|, each with probability |negpow2 n|.  The sampling operation filters the list by the first element (of type
|A|), and then sums the second elements of the result (the probabilities, of type |Q|).

We have so far been unable to show that bind presereves equivalences on the left.  It is highly unlikely that this
property fails to hold, but the indunction hypothesis required for the argument is non-trivial and has so far been
elusive.

An advantage to this approach is that it is trivial to give a list that contains the support, and given decidable
equality on |A| we can compute the precise support.  On the downside, since lists in Agda are necessarily finite, this
approach is only suitable for representing finite distributions.

\section{Continuation-Based Distributions}

An alternative approach is the use of continuation-based distributions, represented by the type |(A -> Q) -> Q|.  A
distribution, represented this way, is a function that takes a measure on |A| and returns the integral over the
probability distribution function over this measure.  This has the advantage of being able to theoretically represent
arbitrary distributions, at the cost of making the representation less amenable to work with.

