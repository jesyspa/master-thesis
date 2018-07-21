\chapter{Interpreting Games}
\label{chp:interpretation}

We have now developed a logic for reasoning about games.  This lets us show that
two games \emph{are} $\epsilon$-indistinguishable, but gives us few tools for
showing that two games \emph{are not} $\epsilon$-indistinguishable remains hard:
we need to argue that no such derivation can be built from an inductive
construction in our logic.  Meanwhile, the very essence of our system relies on
the assumption that an adversary that consistently wins the game can be
distinguished from an adversary that only wins by chance: in other words, we
rely that |coin ==R return true| cannot be shown.

To reason about distinguishability and show that |coin ==R return true| cannot
be derived within our logic, we will look at models of our logic.  In
particular, we will construct a model where we can explicitly refute the |coin
==R return true|.

For the purpose of this chapter, we we will fix the state type |ST| and assume
that it has decidable equality.  As in \autoref{chp:proofs}, we also fix a type
of rational numbers |Q|.

\section{Models of Games}

We try to regard our syntactic model as an object in a certain category.  A
model is then any other object in this category together with a morphism from
the syntactic model to it.  In this case, the category we are looking for is
a monad with two monadic $\epsilon$-relations, where one is weaker than the
other.

We already have one example of a model: the syntactic model defined in
\autoref{chp:proofs}, consisting of a monad |CryptoExpr ST| and two families of
relations |==eE| and |==eR|.  By regarding this as an object in a suitable
category, we can take the coslice category over our syntactic model as our
category of models.

Let $\mathbf{Mod}$ be the category with as objects triples $(M, E, R)$ such that
\begin{itemize}
  \item $M$ is a monad on $\mathbf{Agda}$;
  \item for every object $A$ of $\mathbf{Mod}$, $E_A$ is a $Q$-indexed family of
  binary relations on $M(A)$;
  \item for every object $A$ of $\mathbf{Mod}$, $R_A$ is a ($Q \times
  ST$)-indexed family of binary relations on $M(A)$.
  \item Monadic structure preserves the relations?  Somehow?
\end{itemize}
and as morphisms the monad morphisms that preserve the relations.

Note that we get an initial and a terminal object here.

Anything else here? 

\section{List Model}

We can make an explicit model using a state transformer on a probability monad.
The monad is easy, the distance functions are a bit more annoying, but we can
use the fact we can extract the support to get what we want.

The implementation in Agda is terrible.  Like, really, awful.

We don't know whether this model is complete, from a logical point of view.
Probably not.

\section{Further Work}

There is still considerable work to be done in this area.  There is considerable
engineering work to be done on the list model: many of the desirable properties
require coming up with lemmas we've not yet thought of.






% To write:
% - Let us look at the model theory of games to show this is not trivial.
% - A game structure is a monad + two families of relations.
% - An example of a model.
% - Models in the presence of oracles.
% - An idealisation in the presence of HITs.

