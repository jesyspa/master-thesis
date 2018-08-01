\chapter{A Language for Cryptography}
\label{chp:language}

In the course of the last chapters, we have developed a way of representing
cryptographic games as monadic action, developed an equational theory of
indistinguishability between games, and shown how we can extend and simplify
this with the help of indexed monads.  We have also seen that this construction
can be done in a modular manner using command or interaction structures.  One
question remains: what must be done to turn these developments into a practical
system for reasoning about cryptography?

\section{A Complete System}

There are a number of questions that fall within the scope of this thesis, but
that have not been able to resolve due to time constraints.  We have already
discussed them in greater depth at the end of the relevant chapters, but let us
recap the key points.

In \autoref{chp:proofs}, we defined the notions of an $\epsilon$-normal form and
an $(\epsilon, st)$-normal form for |CryptoExpr|s.  However, we did not prove a
similar result for |OracleExpr|s.  This is unfortunate, as many game-playing
proofs rely on a transformation to this kind of normal form~\cite{gameexamples}.

A planned topic for \autoref{chp:proofs} was the ``identical until bad'' proof
technique~\cite{gameexamples}, which states that if games |X| and |Y| are
different only in the case of a bad event |F| happening, then |X| and |Y| are
$\epsilon$-indistinguishable, with $\epsilon$ being the probability of |F|.
This is a very useful proof step, but we have not found a way to express it in
Agda.  The problem is that the bad event |F| is often implicit in the game: for
example, the event may be ``two calls to |uniform n| return the same bitstring''
or ``the adversary finds a hash collision.''  Instrumenting the game code to
state when |F| occurs can be a non-trivial problem even in concrete cases; a
general solution would be of great value.

In \autoref{chp:command-structures}, we developed the $N$-player implementation
construction and showed how we can systematically fold such an implementation
into a single game.  If an $\epsilon$-relation like indistinguishability was
defined on this game, then this fold gave rise to an $\epsilon$-relation on the
whole implementation.  However, this induced relation is inconvenient to work
with: we would like to be able to express our indistinguishability proofs in
terms of the implementations themselves, and then show via a lemma that the
indistinguishability of their folds follows.  The difficulty lies in striking a
balance between what can be shown and how much bookkeeping this requires.

In \autoref{chp:interpretation}, we present a list-based model of game logic.
We have constructed the carrier of this model in Agda, but we have not verified
all of the properties we require of it.  The proofs involved are typically not
hard conceptually, but require many steps to formulate in Agda.  This suggests
that a proof system for arguments about lists may be an interesting project in
its own right.

Another important issue with this model is the treatment of types that lack
decidable equality.  This issue is made particularly frustrating by the fact
that in cryptography, our problem domain, every value we may want to discuss can
be represented as a bitstring; as such, the question of types without decidable
equality does not arise in practice.  Nevertheless, it is a blemish in our
theory.

The last issue worth mentioning is that our model theory is specified in the
non-indexed case.  We see no fundamental obstacles to generalising the argument
to the indexed case, but we have not done so ourselves.

\section{Further Possibilities}

The greatest obstacle in using the ideas we have presented is the verbosity.
Even in the non-indexed case, expressing the indistinguishability of two games
will typically involve multiple applications of the fact that
indistinguishability is a congruence under bind.  In the indexed case, the
situation is even worse, as the indices may also need to be explicitly
specified.

We expect that reflection could be used to tackle these issues.  Ulf Norell's
\texttt{agda-prelude}\footnote{\url{https://github.com/UlfNorell/agda-prelude}}
library features tactics: these allow the user to write |by pf|, where |pf| is
some equality proof, and allow the library to find a proof of the type expected
by the context.  A similar technique could be used for proofs of
$\epsilon$-indistinguishability to automatically find the applications of
congruence needed to prove a theorem.  The pinnacle of this approach would be to
allow the user to invoke an external SMT solver.

Reflection could also be used to take non-indexed descriptions of games and
generate corresponding indexed versions.  This would free up the syntactic
burden from the programmer, while retaining the extra safety.  However, it is
not clear whether this can be done without considerable loss of expressive
power.

The use of command and interaction structures to simplify the defintion of games
also induces some syntactic burden.  In particular, specifying implementations
and their folds is done in a style that is unfriendly to the user.  A language
with dedicated syntactic constructs for defining an $N$-player implementation
could make the process significantly easier, while still benefiting from our
abstract approach under the hood.

Such a language would benefit from the development of appropriate tooling.  In
our experiments in Agda, we found ourselves repeating the game we were operating
on many times as we made minor changes to it.  These games could (at least
partially) be generated automatically based on the rewrite rules we applied.
However, we were unable to do this within Agda.  This is even more important in
the indexed case, where we do not want to make the user write out every index,
but do want to display this index if the user asks for it.

\section{Conclusions}

In this thesis, we have laid a foundation for a system for reasoning about
indistinguishability in cryptography.  There is still considerable engineerign
work to be done before practical proofs can be expressed, but we nevertheless
consider this a successful proof of concept that shows the viability of a
syntactic approach to this problem.

The primary drawback we have discovered when using Agda is that automating even
very simple proofs is difficult.  In particular, it is not sufficient to specify
what rewrite step we wish to apply, but also precisely where.  This causes
significant duplication, since often almost the entire game has to be written
out as part of the rewrite step.

Another problem arises when we introduce indexing to our games: the correctness
of the code with respect to indices must be specified inline with the code
itself.  For example, if we want to pass a |BitVec n| to a function that takes a
|BitVec k|, we must first provide a proof that |n == k| and then use a rewrite
rule or transport.  This obscures the primary logic of the code; in an ideal
system, we could write the code first and then prove it correct separately.

However, we feel that these issues are primarily ones of presentation, and not
inherent to the approach we are taking.  The usage of $N$-player implementations
to represent the interactions between the challenger, adversary, and oracle
makes it possible to statically enforce constraints on what the players can do,
that are hard to express otherwise.  As far as we know, this usage of command
and interaction structures is novel, and we consider this the primary
contribution of this work.
