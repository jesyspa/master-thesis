\section{Introduction}
\label{sec:introduction}

Cryptographic algorithms are ubiquitous in the modern world, and it is thus important that we can be certain they satisfy
the security guarantees they claim to provide.  In particular, being able to automatically verify that claims of such
proofs are correct is important.  To facilitate this, we aim to develop a framework in which cryptographic algorithms
and proofs of their properties can be expressed.

A number of such frameworks, such as EasyCrypt\footnote{\url{www.easycrypt.info}} and FCF~\cite{fcf}, already exist.  Our
approach is novel in that we use the Agda programming language, which allows us to employ the power of dependent types
in our solution.  In particular, this allows us to express invariants of the algorithm that cannot be expressed in
simpler languages.

We will focus on cryptographic proofs expressed in a game-based manner~\cite{codebasedgames}.  In this setting, a
problem is framed as a game between a \emph{challenger} and an \emph{adversary}.  The challenger represents the
cryptographic algorithm in question, while the adversary represents an attempt to circumvent the security.  An upper
bound on the probability that any adversary wins the game thus corresponds to a statement about the security of this
algorithm.  A proof of such an upper bound typically involves making small modifications to the game, bounding the
difference in victory probability introduced in each, until we arrive at a game where the probability of the adversary
winning is clear.

In this setting, the game, challenger, and adversary are all non-deterministic computations with access to some basic
functionality such as random number generation.  Our approach is to syntactically represent these computations in a free
monad~\cite{freemonads} and then give these terms a valuation in some monad for stateful non-determinsitic
computation, in which we can compute the probability of a certain outcome~\cite{probfunproghaskell}.  By giving an upper
bound on how the total probability is affected by modifications of the syntactic description, we can develop a set of
valid rewriting rules.

There are still a number of issues that we must address in the remainder of the research.  While we have already
formalised a number of lemmas that can be used to show that two games are identical, we have yet to develop a comparable
system for showing that two games are merely very similar.  Furthermore, many existing games involve the adversary
having access to some stateful \emph{oracle}, which can be queried for further information.  We do not yet know how to
represent such oracles within our system, or how to bound the number of times an oracle may be consulted.

We have been able to formalise a proof of the security of the one-time pad encryption scheme against eavesdropper
attacks within our system.  However, even the proof of such a short problem is inconveniently long, and we would like to
research the possibility of using reflection and proof search to reduce the amount of duplication inherent to it.

In the remainder of this proposal, we will introduce cryptographic proofs using games (\autoref{sec:proofs}) and give an
informal example (\autoref{sec:example}), and provide a broad overview of the design choices made so far
(\autoref{sec:work}).  We will then go in more detail on what we hope to achieve in the remainder (\autoref{sec:plan})
and present a timetable for the remainder of the work (\autoref{sec:timetable}).

