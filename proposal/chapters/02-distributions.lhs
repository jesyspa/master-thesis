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

We require a type of probabilities |Q| in order to express statements such as ``the probability of a fair coin landing
heads is $\frac 1 2$''.   A valid implementation is $\mathbb{Q}$, the type of rational numbers, but we allow for slightly
more generality: |Q| need not be a field.

In one sentence, we require |Q| to be a totally ordered commutative ring of characetrestic zero which has negative
powers of two.  The corresponding code, using |Semiring| and |Ord| from the \texttt{agda-prelude} library, is as
follows:
\begin{code}
record Probability (Q : Set) : Set1 where
  field
    overlap {{supersemiring}} : Semiring Q
    overlap {{superord}} : Ord Q
    neg : Q -> Q
    negpow2 : Nat -> Q

  embed : Nat -> Q
  embed zero = zro
  embed (suc n) = one + embed n
\end{code}

The definitions of |Semiring| and |Ord| require that |Q| implement |_+_|, |_*_|, |zro|, |one|, |_<_|, and |compare|.

This choice of requirements on |Q| implies that |Q| contains some elements (e.g. |plus one one|) that are not valid
probabilities.  We consider this a worthwhile trade-off: when we use these operations, we often know a priori that the
result will be a probability due to how we choose our summands.  Having to prove this fact to be able to formulate the
computation would be a needless complication, since we can do the same proof separately if we need to.  The primary
downside is that it is harder to state that some property holds for every probability, but this is irrelevant for us
since we will typically not be making such statements.

Another consequence of this choice is that the |compare| operation imposes a \emph{decidable} total order on |Q|, which
precludes us from using a formalisation of $\mathbb{R}$ as a model.  Since we are interested exclusively in discrete
probability distributions, we do not expect this to be an issue.  Furthermore, due to the way the order is used, we
expect that this requirement could be removed.

Having established the operations, we specify the properties that the type must satisfy.  We use the usual axioms for an
ordered commutative ring, augmented with the requirement that |negpow2 n| be the multiplicative inverse of |pow2 n|, and
the requirement that |embed| be injective.

We express this in Agda by fixing |Q| and an instance of |PQ : Probability Q| (for example, by taking these as module
parameters) and defining
%{
%format srprops = "\RF{ring-props}"
%format poprops = "\RF{order-props}"
%format SemiringProps = "\F{RingProps}"
%format PreorderProps = "\F{OrderProps}"

%format mulcomm = "\RF{*-comm}"
%format negisinv = "\RF{neg-is-+-inv}"
%format embedInj = "\RF{embed-Inj}"
%format plusorder = "\RF{+-preserves-order}"
%format mulorder = "\RF{*-respects-order}"
%format pow2cancel = "\RF{pow2-negpow2-cancel}"
\begin{code}
record ProbabilityProps : Set where
  open Probability PQ
  field
    overlap {{srprops}}  : SemiringProps
    overlap {{poprops}}  : PreorderProps
    mulcomm              : (a b : Q) -> (times a b) == (times b a)
    negisinv             : (a : Q) -> zro == (plus a (neg a))
    embedInj             : Injective embed
    plusorder            : (a b c : Q) -> a < b
                         -> (plus a c) < (plus b c)
    mulorder             : (a b : Q) -> zro < a -> zro < b
                         -> zro < (times a b)
    pow2cancel           : forall n -> one == (times (embed (pow2 n)) (negpow2 n))
\end{code}

We assume that |SemiringProps| and |PreorderProps| are also specific to |Q| and |PQ|.

Up to now, most of our work has only used the semiring structure of probabilities.  The additive inverse and order will
become important when we look at non-perfect security, at which point we may need to augment this with further
assumptions.

An important consideration is whether we wish to allow uniform distributions over an arbitrary finite set, and (more
strongly) whether we wish to allow the repetition of a (stateless) computation until some condition is satisfied.  The
former corresponds with requiring the existence of multiplicative inverses for all (embedded) natural numbers, while the
latter corresponds to requiring the existence of multiplicative inverses for all non-zero elements.
%}

While it would certainly be amusing to find an argument that benefited from choosing an unusual structure such as a
matrix or polynomial ring for the type of probabilities, we do not consider this likely.  Our motivational example is
still $\mathbb{Q}$, and we consider any statements that (constructively) hold for $\mathbb{Q}$ to be admissible
extensions of this set of requirements.

\section{Distributions: Abstract Specification}

We will now provide a similar description for the notion of a distribution. 
\begin{code}
record DistMonad (D : Set → Set) : Set₁ where
  field
    probability : Set
    uniform : forall n -> D (BitVec n)
    sample : forall {A} -> {{_ : Eq A}} -> D A -> A -> probability
    overlap {{probability-super}} : Probability probability
    overlap {{monad-super}} : Monad D
  infix 4 _==D_
  _==D_ : forall {A} -> {{_ : Eq A}} -> D A -> D A -> Set
  _
  coin : D Bool
  coin = fmap head (uniform 1)
\end{code}

We will now assume a type |Q| of probabilities with an associated |PQ : Probability P|, but will be explicit about when
we also assume the existence of a |PPQ : ProbabilityProps|.  Our construction here will mimic the construction in the
previous section; we will present a |record Distribution| that specifies the operations a distribution must support, and
then a secondary |record DistributionProps| that specifies the laws that a distribution must satisfy.

A distribution is 

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

