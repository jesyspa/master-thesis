\chapter{Interpreting Games}

Now that we have a syntax for games, we can define an interpretation of games.
The fundamental idea is that we can regard a game, that is a term of type
|CryptoExpr A|, as a stateful probabilistic computation which gives a result of
type |A|.  We construct a monad that represents such stateful probabilistic
computations and allows us to compute the probability of getting any specific
result.  This allows us to reason about when two games describe probabilistic
computations that give the same result with high probability, and define a
similarity relation based on this.

\section{The Dist Monad}

I think that in the full version of the thesis it is worth writing out
explicitly what properties we expect our distribution monad to satisfy.  The
implementation can generally be skimmed over, referencing existing work, but the
conditions imposed should be covered.

This area is more technical than insightful in many places (e.g. working with
finite sets), so deferring it to an appendix may also be reasonable.  I will
probably want a page or two just stating (in Agda) all the laws, and that's not
to mention how we work with the rationals.  In fact, the rationals can be an
appendix in their own right.

\section{The Valuation}

Now that we have a distribution monad |Dist|, once we have chosen some oracle
state type |OracleState|, we can use |StateT (OracleState * AdvState) Dist| to
interpret the distribution if we have an implementation of the oracle.  We
denote this monad by |StateDist|.  This gives us the following:

\begin{code}
record OracleImpl : Set where
  field
    InitImpl : OracleInit -> StateDist top
    CallImpl : OracleArg -> StateDist OracleResult

evalCE : OracleImpl -> CryptoExpr A -> StateDist A
\end{code}

This function arises from the fact that |CryptoExpr| is a free monad, since we
have interpretations for all the operations.

Note that the oracles have direct access to |StateDist|; their types alone do
not require them to return well-behaved distributions.  We should do something
about that.  In particular, we don't want the oracle inspecting the adversary
state.

\section{The Indistinguishability Relation}

We now have a notion of indistinguishability for terms of type |M A| with |A|
finite.\footnote{Perhaps doing something with the support would also be
interesting?} Since we apply a state monad on top of |Dist|, we want to
generalise this notion to terms of type |S -> M (A * S)|.

Note that simply assuming |S| has decidable equality and taking the maximum over
all |s : S| would not work: for every $\epsilon$, the adversary could choose a
state type so that $\abs{S}^{-1}$ is much smaller than $\epsilon$.  By
scrambling the state on every computation, the difference between any two
outcomes becomes less than $\epsilon$, and so we cannot show that e.g. |return
false| and |return true| are different.  Taking the sum over all |S| works,
though.

Another consideration is that when we regard the game as a whole, we don't want
to worry about the initial and final states.  We thus require the adversary to
specify their initial state and we project away the final state.
