\chapter{Game-Playing Proofs}

Now that we have sketched the overarching ideas of the thesis and their technical implementation, let us return from the
formalised treatment and see what techniques and results come up when studying cryptographic algorithms via games.  The
goal of this chapter is to familiarise the reader with a number of games that are important in cryptography, together
with some approaches that can be used to prove results about them.  This should additionally serve as motivation for
pursuing this line of research further, since not everything presented here will be expressible in terms of the
machinery we have so far outlined.

\section{Notions and Definitions}

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

\subsection{Security Levels}

We have mentioned that depending on the requirements of the situation, we may want consider a scheme secure if
the adversary's advantage is always zero, or if it is bounded by a constant, or if it is bounded by a function vanishing
asymptotically in some security parameter.  In the discussion of the above games, we omit discussion of this: each of
the games can have any of these three conditions imposed upon it externally.  In the asymptotic case, we assume that the
entire construction is parametrised by this parameter.  Simililarly, we can impose polynomiality constraints upon these
definitions.  In all cases, we express that these bounds are satisfied by saying that the advantage is negligible.

\subsection{Oracles}

We have avoided the discussion of oracles up to this point, since their implementation in Agda is still an open
question.  However, since oracles play an essential role in the proofs that we will be formalising, we will show several
uses of them in this chapter.

Simply speaking, an oracle is a stateful function that the adversary gains access to.  The adversary may query the
oracle, but may not inspect its state.  Furthermore, many proofs rely on counting the number of times an oracle is
accessed, expressing the advantage in terms of this number to show that if the number of queries is fixed (or
polynomial) in the security parameter, then by increasing the security parameter we can make the adversary's advantage
neglegible.

\section{Important Games}

There are a number of games which will be running examples in the rest of the presentation.  We will describe them
informally here to simplify their presentation when we tackle them formally later on.  These games should also motivate
the necessity of (stateful) oracles and 

\subsection{Indistinguishability Games}

The simplest form of game is one where given two classes $X$ and $Y$ of objects of the same type |T|, the
advantage of an adversary |A : T -> Bool| is
\[
    |\mathbb{P}_{x \in X}[ A x ] - \mathbb{P}_{y \in Y}[ A y ]|.
\]

We say that the classes $X$ and $Y$ are indistinguishable if the advantage is negligible.

A minor variation on this game is when |T| is a function type, and instead of giving it as a parameter we provide it to
the adversary as an oracle:
\[
    |\mathbb{P}_{f \in X}[ A^f ] - \mathbb{P}_{g \in Y}[ A^g ]|.
\]

The adversary then is a parameterless probabilistic computation, which may call the oracle.  From the point of view of
the adversary, there is no difference between receiving a (stateless) oracle and a simple function, but choosing one
game over the other may lead to proofs being more convenient.  (If we were to work with deep embeddings of adversaries,
we could rewrite an adversary taking an oracle into an adversary taking a function and vice-versa, but this would make
adversaries and proofs much harder to express.)

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

A slightly stronger attack than the Eavesdropper attack is the Chosen-Plaintext attack, where the adversary has access
to 

\subsection{Chosen-Ciphertext Attack}

\section{Example Proofs}

\subsection{ElGamal Encryption}

\subsection{Pseudorandom Functions}

\section{Proof Techinques}

