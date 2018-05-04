\section{Research Plan}
\label{sec:plan}

Although the system developed so far can already be used to express non-trivial results like the One-Time Pad proof
above, considerable work must still be done in order to be able to prove more complex properties.  There are three
points on which we will need to focus in particular: adversaries with oracle access, sub-perfect security, and proof
automation.

\subsection{Oracles}

All games we have seen so far have been between a challenger and an adversary.  Sometimes, it is interesting to consider
additional stateful players.  The simplest form of this is by introducing oracles, which respond to queries given by the
adversary.  In the Chosen Plaintext Example, we could represent the adversary's access to the encryption function by
specifying that there is an oracle that responds to encryption queries.

The introduction of oracles presents a new difficulty: it is important that the adversary cannot obtain too much
information from these oracles.  In particular, we want oracle state to be inaccessible to the adversary and we may want
to bound the number of queries that the adversary may perform.

We are considering two approaches for limiting access to oracle state.  The first is to require that the adversary be
polymorphic over the type of state the adversary stores.  This ensures, by a free theorem~\cite{freetheorems}, that the
adversary cannot in any way depend on the oracle state.  The downside of this is that this free theorem is not provable
within Agda and must thus be postulated.  The other approach, which is more complicated but does not require postulates,
is to provide the challenger, adversary, and oracles with different sets of operations in the game syntax, making it
syntactically impossible to express adversaries that inspect the oracle state.

It is so far unclear how the number of queries to an oracle can be bounded.  We are considering using the oracle state
to store a counter of the number of uses, or making oracle calls a primitive syntactic operation that could then be
counted by inspecting the adversary game.

\subsection{Security Levels}

In practice, many cryptographical algorithms lack perfect security but are nevertheless interesting and practically
useful.  We can express weaker notions of security by relaxing the requirement of indistinguishability or by requiring
that the result only hold for a particular class of adversaries.

In the examples so far, we said that a game was unwinnable if the advantage of every adversary was exactly zero.  We can
weaken this statement by only requiring that the advantage by bounded by some $\epsilon$ (possibly dependent on the
security parameter).  Unfortunately, it is not clear how to bound the change in advantage in the overall game when
perfroming a small modification to some step.  Formulating and proving rewrite lemmas for this setting is one of the
primary goals for the remainder of this research.

The other way in which security can be relaxed is by only considering adversaries that satisfy particular properties;
a common choice is the class of adversaries that perform only a polynomial amount of computation, or only polynomially
many oracle queries.  Since we have chosen to avoid a deep embedding, it is unlikely that we will be able to bound the
amount of computation, since we cannot inspect how much computation an Agda function performs.  However, with further
research, we may be able to bound the number of oracle queries that the adversary performs.

\subsection{Proof Automation}

Expressing even simple proofs in the framework we have so far developed is too verbose to be of practical use.  For a
large part, this is due to every step having to express not only what changes, but also the full context of the change.
Although this context can be computed from the game terms that we are reasoning about, Agda's implicit argument
mechanism cannot deduce them.  In order to nevertheless automatically generate the necessary proofs, we could use
reflection to specify a proof search algorithm specialised for this case.

This approach can be split into two sections: obtaining a quoted representation of the game, and finding where in that
representation we can apply a given equality.  The first problem relies heavily on the implementation of reflection in
Agda, while the second is independent, requiring only a representation of quoted terms.  Both are viable additions to
the project.  We are hesitant to embark on the first, since Agda's reflection machinery is occasionally changed, making
the usefulness less certain.  The second, however, is of theoretical interest by itself.

\subsection{Practical Examples}

In addition to the general developments described above, we also consider it important to prove the usefulness of this
system by formalising a number of existing proofs where it is possible, and identify the problems where it is not.  In
particular, the examples presented by Shoup~\cite{gameexamples} would be a good starting point to prove that the system
is sufficiently versatile to be of practical interest.


