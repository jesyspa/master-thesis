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

Now we can say that two games are indistinguishable with respect to an oracle
implementation if their evaluations are indistinguishable.

Given bounds on how similar oracles are, we can bound the difference of the same
game with two different oracle implementations, as long as we bound the number
of calls to init and impl.

