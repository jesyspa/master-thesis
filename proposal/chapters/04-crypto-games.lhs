\chapter{Game-Playing Proofs}

Now that we have sketched the overarching ideas of the thesis and their technical implementation, let us return from the
formalised treatment and see what techniques and results come up when studying cryptographic algorithms via games.  The
goal of this chapter is to familiarise the reader with a number of games that are important in cryptography, together
with some approaches that can be used to prove results about them.  This should additionally serve as motivation for
pursuing this line of research further, since not everything presented here will be expressible in terms of the
machinery we have so far outlined.

\section{Important Games}

We have chosen not to given a rigorous definition of a game; in some sense, a game is anything we wish to treat as one.
However, it is worth noting that there are two essential properties that a game should have to be meaningful:
\begin{enumerate}
    \item The game should be parametrised over some notion of an \emph{adversary}, and
    \item There should be a measure of how well the adversary performs, the adversary's \emph{advantage}.
\end{enumerate}

We will typically argue informally that if the adversary's advantage in a certain game can be bounded, then some
property we are interested in holds: for example, in chapter~\ref{chp:introduction} we argued that if the Eavesdropper
advantage of an encryption scheme is zero, then Eve gains no new information by intercepting a single message that Alice
sent to Bob.  We will then use a sequence of games to demonstrate that such a bound does indeed exist.  This thesis is
concerned primarily with the second part of the argument, since the first is generally not readily formalisable.

Remark: we have mentioned that depending on the requirements of the situation, we may want consider a scheme secure if
the adversary's advantage is always zero, or if it is bounded by a constant, or if it is bounded by a function vanishing
asymptotically in some security parameter.  In the discussion of the above games, we omit discussion of this: each of
the games can have any of these three conditions imposed upon it externally.  In the asymptotic case, we assume that the
entire construction is parametrised by this parameter.  Simililarly, we can impose polynomiality constraints upon these
definitions.  In all cases, we express that these bounds are satisfied by saying that the advantage is negligible.

\subsection{Indistinguishability Games}

The simplest form of game is one where given two classes $X$ and $Y$ of objects of the same type |T|, the
advantage of an adversary |A : T -> Bool| is
\[
    |\mathbb{P}_{x \in X}[ A x ] - \mathbb{P}_{y \in Y}[ A y ]|.
\]

We say that the classes $X$ and $Y$ are indistinguishable if the advantage is negligible.

A minor variation on this game is when |T| is a function type, and instead of giving it as a parameter we provide it to
the adversary as an \emph{oracle}:
\[
    |\mathbb{P}_{f \in X}[ A^f ] - \mathbb{P}_{g \in Y}[ A^g ]|.
\]

The adversary then is a parameterless probabilistic computation, which may call the oracle.  The advantage of this
approach is that queries to the oracle can be inspected with more nuance than simple calls to a function.  In
particular, we hope to be able to express an upper bound on the number of oracle queries an adversary performs.
Furthermore, an oracle computation may maintain state that the adversary cannot access.  Later in this chapter, we will
give an example of a use of this.

These games are not very interesting to study directly, but are useful tools for expressing assumptions.  For example,
we say that $F$ is a pseudo-random class of functions if it is indistinguishable from the set of all functions.  This
example also illustrates that the classes $X$ and $Y$ need not be disjoint.

\subsection{Eavesdropper Attack}

The Eavesdropper attack was already shown in Chapter~\ref{chp:introduction}.  Informally, we can state it as follows.
The challenger possesses a key generation function and an encryption function.  The challenger generates a key $k$, and
takes two messages $(m_0, m_1)$ from the adversary, flips a coin with result $b$, encrypts $m_b$ with $k$, and gives the
result $c$ to the adversary.  The adversary returns a boolean $b'$.  The adversary's advantage is
\[
    |\mathbb{P}[ b = b' ] - \mathbb{P}[ b ]|.
\]

In other words, the advantage is how much better the adversary can do than random chance.

We can regard the Eavesdropper attack as a variation on the indistinguishibilty game where the adversary may choose two
`seed' messages $(m_0, m_1)$ that give rise to the classes $E(m_1)$ and $E(m_2)$, consisting of ciphertexts of $m_0$ and
$m_1$.  The adversary advantage is the advantage the adversary has playing the indistinguishibility game between
$X = E(m_0)$ and $Y = E(m_1)$.

\subsection{Chosen-Plaintext Attack}

\subsection{Chosen-Ciphertext Attack}

\section{Example Proofs}

\subsection{ElGamal Encryption}

\subsection{Pseudorandom Functions}

