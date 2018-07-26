\chapter{Interpreting Games}
\label{chp:interpretation}

With the logic we have developed in hand, we can tackle questions about games
being $\epsilon$-indistinguishable.  However, if we are to be convinced that our
results have any meaning, we must first show that our system is at the very
least not trivial: if \emph{every} game |ce : CryptoExpr ST Bool| could be shown
to be $\epsilon$-indistinguishable from |coin| then our proof would have little
weight behind it.  It would be even better if we could show that our notion of
indistinguishability can be expressed as a relation on probability
distributions.

To this end, we will define the notion of a \emph{model} of our logic and
construct a non-trivial model based on the Haskell |Dist| monad due to Erwig and
Kollmansberger~\cite{probfunproghaskell}.  Using this model, we can show that
our logic does not prove |coin ==R return true| or |return false ==R return
true|.

For the purpose of this chapter, we we will fix the state type |ST| and assume
that it has decidable equality.  As in \autoref{chp:proofs}, we also fix a type
of rational numbers |Q|.

\section{Models of Game Logic}

We have already found one model for our logic: the syntactic model, consisting
of a monad |CryptoExpr ST| together with a monadic $\epsilon$-relation |==eE|
and a functorial $\epsilon$-relation |==eR|.  We will denote this model by
|CE|. Our definition of a relation is a direct generalisation of this.

\begin{definition}
  A \emph{model of game logic} is a monad |M| together with a monadic
  $\epsilon$-relation |~~eE|, a functorial $\epsilon$-relation |~~eR|, and a
  valuation function |VAL _ : CryptoExpr ST A -> M A| such that |~~eE| is a
  subrelation of |~~eR| and for any games |ce| and |cf|,
  \begin{itemize}
    \item if |ce ==eE cf|, then |(VAL ce) ~~eE (VAL cf)|; and
    \item if |ce ==eR cf|, then |(VAL ce) ~~eR (VAL cf)|.
  \end{itemize}
\end{definition}

This definition can be rephrased in categorical terms by considering the
syntactic model in a suitable category and taking the coslice:

\begin{definition}
  Let $\PreMGL$ (pre-models of game logic) be the category whose
  objects are monads |M| together with a monadic $\epsilon$-relation |~~eE| and
  a functorial $\epsilon$-relation |~~eR|, where |~~eE| is a subrelation of
  |~~eR|, and whose morphisms are monad morphisms that preserve the structure of
  both relations.
\end{definition}

Recall that given a category $\mathcal{C}$ and an object $A$ of $\mathcal{C}$,
the coslice category (or under category) $A \shortdownarrow \mathcal{C}$ is the
category where the objects are morphisms out of $A$ (in $\mathcal{C}$), and the
morphisms from an object $\phi : A \to B$ to $\psi : A \to C$ are morphisms $f :
B \to C$ such that $f \circ \phi = \psi$.

Let us now enote the coslice category $CE \shortdownarrow \PreMGL$ by
$\MGL$.

\begin{theorem}
  A model of game logic $\mathcal{M}$ is an object in $\MGL$.
\end{theorem}

\begin{proof}
  Let $\mathcal{M}$ be a model of game logic.  The underlying monad and the
  $\epsilon$-relations give rise to an object in $\PreMGL$.  The
  valuation function gives a monad morphism which, by definition of a model of
  game logic, preserves the $\epsilon$-relations.

  On the other hand, let $\mathcal{M}$ be an object in $\MGL$.  Its
  codomain is a $\PreMGL$ object.  Regarding $\mathcal{M}$ as a
  valuation function, this gives rise to a model of game logic.
\end{proof}

This result allows us to use standard theorems about coslice categories to
analyse the model theory of game logic.  In particular, it tells us that the
identity function on |CE| is the initial object in $\MGL$, meaning that
our syntactic model is initial, as we would expect.  Furthermore, since
$\PreMGL$ has a terminal object $1$ (given by the constant singleton
monad), the unique map from |CE| to $1$ gives us a terminal model.  In general,
limits in $\MGL$ correspond to the limits of the underlying objects in
$\PreMGL$~\cite{maclane}.

\section{List Model}

\todo{Clarify how incomplete things are.}
Let us now regard a specific model based on the |Dist|
monad~\cite{probfunproghaskell}, in which we can compute whether two games over
a finite type |A| are $\epsilon$-indistinguishable.  This material has not been
fully worked out in Agda, but the claims we make pertain to finite objects
(lists of rational numbers) and, as such, can be shown to hold constructively.
Furthermore, the construction relies in several places on equality being
decidable.  This is a serious issue.  However, we think that the results we
present here are worth stating despite this. For now, we will assume that all
types involved have decidable equality, and analyse this assumption at the end
of this section.

We represent a probability distribution over a type |A| as a list of pairs of
elements of |A| and their corresponding probabilities.  Our two basic
distributions, |return a| and |coin|, can thus be represented as follows:
\begin{code}
  return : A -> Dist A
  return a = (a , 1) :: []

  coin : Dist Bool
  coin = (false , 1/2) :: (true , 1/2) :: []
\end{code}

Any uniform distribution can be constructed by repeated calls to |coin|.
We can define bind as follows:
\begin{code}
  [] >>= f = []
  ((a , p) :: xs) >>= f = map (times p) (f a) ++ (xs >>= f)
\end{code}

The resulting |Dist| monad structure is in fact isomorphic to the |WriterT (Q ,
times) List| monad.  We use the latter in our implementation, as it allows for
better separation of concerns; in particular, the monad laws for |Dist| follow
from the monad laws for |Writer| and |List|.  However, the difference is
insignificant to us here, and the direct presentation is clearer.

There is a slight complication that we need to address here.  We require that an
$\epsilon$-relation on $A$ identify every two elements of $A$ at $\epsilon = 1$.
We would like to define the $\epsilon$-indistinguishability relation on
distributions with the help of a distance function, much as we did in
\autoref{sec:proofs-dists}.  However, this definition fails if we allow
`distributions' with negative elements, or `distributions' that sum to more than
1.

In order to deal with this problem properly, we would need to have every
distribution carry around a proof of its validity.  However, this is very
inconvenient from a programming perspective: these proofs must be maintained at
all times, which makes it inconvenient to perform recursion on the list
structure.  As such, it is more convenient to instead make a separate type
|ValidDist xs| that represents a proof that |xs| is a valid distribution.  We
can then show that validity is preserved by bind.  Our implementation lacks this
feature, but as we will see, the reliance on these assumptions is minor.

For the purposes of this section, we will continue to work with the |Dist| monad
but assume that any distribution |xs| has a corresponding |ValidDist xs| proof.

The concrete nature of |Dist| allows us to provide two further operations that
are not supported by |CryptoExpr ST|: computing the support of a distribution
and the probability of drawing a specific element.

Since we have assumed that all types we are dealing with have decidable
equality, we can define a function |uniques : List A -> List A| that, given a
list, returns the list of unique elements it has.  We can then define
\begin{code}
  support : Dist A -> List A
  support xs = uniques (map fst xs)
\end{code}

Computing the probability of sampling a particular element is a matter of
finding all occurences of this element and summing the corresponding
probabilities:
\begin{code}
  sample : Dist A -> A -> Q
  sample xs a = sum dollar map snd dollar filter (isYes . (eq a) . fst) xs
\end{code}

We can now verify that our definition of bind corresponds to the one defined in
\autoref{sec:proofs-dists}.

\begin{theorem}
  For every |xs : Dist A|, |f : A -> Dist B| and |b : B|, the following 
  expression is equal to |sample (xs >>= f) b|:
  \begin{code}
    sum dollar map (\ a -> times (sample xs a) (sample (f a) b)) (support xs)
  \end{code}
\end{theorem}

This is a result we have been unable to show in Agda.  The difficulty lies in
finding a suitable value to perform induction on: in our attempts, neither |xs|
nor |support xs| provided enough structure to carry through the argument.
\todo{Discuss more about this?}  This is made only all the more frustrating by
how simple the proof is on paper:

\begin{proof}
  \todo{It's the same sum in two different ways.}
\end{proof}

The monad |Dist| provides us with a suitable interpretation of probability, but
it does not allow us to interpret stateful computations.  For this last
functionality, we use the |StateT ST| monad transformer.  Since this is a monad
transformer, |coin| lifts into it, and we use the usual |getState| and
|setState| to interpret the corresponding operations.  As we have seen in
\autoref{chp:command-structures}, specifying these there base operations extends
to a unique monad morphism from |CryptoExpr ST| to |StateT ST Dist|.

As above, we assume that given |g : StateT ST Dist A|, for any |st : ST|, |g st|
is a valid probability distribution with a corresponding proof |ValidDist (g
st)|.

We can now define a notion of distance between distributions.  We make use of a
|union| function that merges two lists and removes duplicates.
\begin{code}
distance : (xs ys : Dist A) -> Q
distance xs ys = times (1/2) (sum (map (\ a -> sample xs a - sample ys
a) sup))
  where sup = union (support xs) (support ys)
\end{code}

We say that |g1 ~~eE g2| iff for every |st : ST|, |distance (g1 st) (g2 st) <=
epsilon|.

\begin{theorem}
  |~~eE| is an $\epsilon$-relation.
\end{theorem}

\begin{proof}
  TODO: Sketch
\end{proof}

We say that |g1 ~~eR g2| iff |distance (fst dollar g1 st) (fst dollar g2 st) <=
epsilon|.

\begin{theorem}
  |~~eR| is an $\epsilon$-relation.
\end{theorem}

\begin{proof}
  TODO: Sketch
\end{proof}

\todo[inline]{Discuss preservation of relations}

Throughout this section, we have assumed that every type has decidable equality.
This is, of course, not the case.  It is not clear how we can best deal with
this.  The following trick allows us to nevertheless define the |~~eE| and
|~~eR| relations: for |g1| and |g2| in |StateT ST Dist A|, we say that |g1 ~~eE
g2| iff for every |st : ST| \emph{and every proof that |A| has decidable
equality}, |distance (g1 st) (g2 st) <= epsilon|.  This is a type that behaves
as our earlier definition for decidable |A|.  However, we cannot prove
properties such as congruence under |fmap| if indistinguishability is defined
this way.

Another option is to only define indistinguishability for result types that have
decidable equality.  This, however, means that this is no longer a model of game
logic.

Yet another option is to require finiteness of the state type and regard our
|StateT ST Dist| functor as an endofunctor on the category of sets with
decidable equality.  This requires the additional assumption of functional
extensionality.  At present, this is the cleanest solution, but it is not clear
whether all games we may want to express can be expressed this way.

\section{Future Work}

TODO: Finish off list model, develop continuation-passing model, explore
possibility of other models, explore completeness properties.

One possible avenue of development relates to the definition of a model of game
logic.  As we have seen in \autoref{chp:command-structures}, a monad morphism
|CryptoExpr ST A -> M A| is completely determined by its action on the base
operations |Uniform|, |GetState|, and |SetState|.  It is thus sufficient to
require the existence of the terms |uniform|, |getState|, and |setState|, since
the valuation is then obtained by taking the unique extension to a monad
morphism.  However, the preservation conditions nevertheless require considering
arbitrary games.  If the preservation conditions could be reformulated to not
refer to such games, this could considerably simplify the construction of
models.

