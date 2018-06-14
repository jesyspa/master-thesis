\chapter{Interpreting Games}

The fundamental idea is that we can regard a game, that is a term of type
|CryptoExpr A|, as a stateful probabilistic computation which gives a result of
type |A|.  We construct a monad that represents such stateful probabilistic
computations and allows us to compute the probability of getting any specific
result.  We then define two computations to be similar if the probability of
their interpretations giving different results is small.

A considerable problem is the implementation of oracles.  Namely, we don't have
any guarantee that oracles actually have nicely-behaving distributions: they are
not (as far as the type system is concerned) necessarily constructed using the
base combinators, like the challenger and adversary are.  On the other hand,
this code is known and thus we can prove it for every individual case.  Still, I
think this can be used as good motivation to introduce interaction structures.

