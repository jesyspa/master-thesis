\chapter{Introduction}

This thesis is structured as follows: we start by demonstrating how games can be
used in cryptography, then show how these can be represented and reasoned about
in Agda, and how common steps used in cryptography\footnote{Triple Encryption
paper} can be formalised in this manner.  We then detour into indexed monads and
interaction structures and show how these can be used to more precisely express
the computations we are interested in.  Finally, we give an overview of how
these developments could be combined in order to provide a language for
reasoning about games.

The goal of this chapter is to introduce the problem that we are trying to
formalise.  This means that it should cover not only the basic question of what
a game is and how we reason about it, but also introduce the notion of an
oracle.

Depending on how far I get in terms of defining a language for games, I can use
that here to express the proofs in a more formal way.  (Depends also on how
intuitive it becomes: if it needs extensive introduction itself, this won't
work.)

\section{Motivation for Games}

In cryptography, we often wish to prove that a certain function does not exist.
The prototypical example is when we want to show an encryption scheme is secure:
we want to show that no function exists that (with high probability) correctly
decrypts messages without knowledge of the key.

Questions of this form can be rephrased as games between a challenger and an
adversary: in this case, the adversary chooses two messages, the challenger
encrypts one, and the adversary must identify which of the messages was
encrypted.  The adversary wins if he guesses correctly.  How much better the
adversary can perform than random chance is called the adversary's
\emph{advantage}, and we can now reformulate our goal from proving non-existence
to the finding of an upper bound on the advantage.

There are some games where this upper bound is clear.  For example, if the
challenger flips a coin and the adversary wins if it comes up heads, the
adversary has no active participation and so any adversary will have equal
probability of winning (and thus advantage 0).  For more complicated games, we
derive the upper bound by relating them to such simpler games.

\section{Example: One-Time Pad}

This section can be taken almost entirely from the proposal, except that I want
to phrase it in Agda this time.

\section{Oracles}

Sometimes, we want to give the adversary access to some extra computation they
may perform.  This is typically called an oracle.  For example, the adversary
may be given access to the encryption function.  We could give the adversary the
function explicitly.  However, some oracles are stateful: for example, they may
use a pseudo-random number generator, or store the queries already performed by
the adversary.  As such, we should not allow the adversary to get or set this
state, and want to force the adversary to use the oracle only as a black box.


\section{Example: PRFs (?)}
