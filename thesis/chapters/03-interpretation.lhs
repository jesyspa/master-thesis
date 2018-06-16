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

Now that we have a distribution monad |Dist|, we can use |StateT (OracleState *
AdvState) Dist| to interpret the 


A considerable problem is the implementation of oracles.  Namely, we don't have
any guarantee that oracles actually have nicely-behaving distributions: they are
not (as far as the type system is concerned) necessarily constructed using the
base combinators, like the challenger and adversary are.  On the other hand,
this code is known and thus we can prove it for every individual case.  Still, I
think this can be used as good motivation to introduce interaction structures.

