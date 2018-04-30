\section{Research Plan}
\label{sec:plan}

Although the system developed so far can already be used to express non-trivial results like the One-Time Pad proof
above, considerable work must still be done in order to be able to prove more complex properties.  There are three
points on which we will need to focus in particular, namely sub-perfect security, adversaries with oracle access, and
proof automation.

\subsection{Security Levels}

In practice, many cryptographical algorithms lack perfect security but are nevertheless interesting and practically
useful.  We can express weaker notions of security by relaxing the requirement of indistinguishability or by requiring
that the result only hold for a particular class of adversaries.

In the examples so far, we said that a game was unwinnable if the advantage of every adversary was exactly zero.  We can
weaken this statement by only requiring that the advantage by bounded by some $\epsilon$ (possibly dependent on the
security parameter).  Unfortunately, while this change is simple at the level of games, proving results in this new
setting requires a weaker notion than strict indistinguishability.  Further research is needed to find what the
appropriate notion is.

The other way in which security can be relaxed is by only considering adversaries that satisfy particular properties;
typically, that the amount of computation of number of queries that the adversary does is bounded by a polynomial in the
security parameter.  Since we have chosen to avoid a deep embedding, it is unlikely that we will be able to bound the
amount of computation, since we cannot inspect how much computation an Agda function performs.  However, with further
research, we may be able to bound the number of oracle queries that the adversary performs.

\subsection{Oracles}

All games we have seen so far have been between a challenger and an adversary.  Sometimes, it is interesting to consider
additional stateful players.  The simplest form of this is by introducing oracles, which respond to queries given by the
adversary.  In the Chosen Plaintext Example, we could represent the adversary's access to the encryption function by
specifying that there is an oracle that responds to encryption queries.

The introduction of oracles presents a new difficulty: it is important that the adversary cannot obtain too much
information from these oracles.  In particular, we want oracle state to be inaccessible to the adversary and we may want
to bound the number of queries that the adversary may perform.

We are considering two approaches for limiting access to oracle state.  The first is to require that the adversary be
polymorphic over the type of state the adversary stores.  This ensures, by a theorem~\cite{freetheorems}, that the
adversary cannot in any way depend on the oracle state.  The downside of this is that this free theorem is not provable
within Agda and must thus be postulated.  The other approach, which is more complicated but does not require postulates,
is to provide the challenger, adversary, and oracles with different sets of operations in the game syntax, making it
syntactically impossible to express adversaries that inspect the oracle state.

It is so far unclear how the number of queries to an oracle can be bounded.  We are considering using the oracle state
to store a counter of the number of uses, or making oracle calls a primitive syntactic operation that could then be
counted by inspecting the adversary game.

\subsection{Proof Automation}

As can be seen from the One-Time Pad example, expressing even simple proofs in the framework we have is too verbose to
be of practical use.  For a large part, this is due to every step having to express not only what changes, but also the
full context of the change.  In particular, significant duplication is caused by the |congbind| rule that allows us to
conclude |x >>= f| is indistinguishable from |x >>= g| if |f a| and |g a| are indistinguishable for all |a|: if |f| and
|g| are lambda terms then Agda cannot autodeduce them.  The entire right-hand side of each |>>=| to the left of the
changed term must be written out, giving a quadratic explosion in proof sizes.

One approach to reducing this problem is to not employ lambda terms when describing games.  This would allow us to
leverage the implicit argument feature of Agda for some of this work, but would require step-by-step descriptions of the
games to be written out separately.  The definition of each game would also be broken up, making it harder to regard
them in their entirety.

A more hopeful approach is to use reflection so that given an equality and a game, we can quote the game, inspect the
structure, and find where in the body we can perform a substitution using that equality.  We can then generate a proof
term based on this quoted representation, that can be unquoted to give an equality between games.

This approach can be split into two sections: obtaining a quoted representation of the game, and finding where in that
representation we can apply a given equality.  The first problem relies heavily on the implementation of reflection in
Agda, while the second is independent, requiring only a representation of quoted terms.  Both are viable additions to
the project, though we regard the latter as of more theoretical interest.

\subsection{Practical Examples}

In addition to the general developments described above, we also consider it important to prove the usefulness of this
system by formalising a number of existing proofs where it is possible, and identify the problems where it is not.  In
particular, the examples presented by Shoup~\cite{gameexamples} would be a good starting point to prove that the system
is sufficiently versatile to be of practical interest.


