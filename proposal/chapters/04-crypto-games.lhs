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
property we are interested in holds: for example, in chapter~\ref{chp:introduction} we argued that if the eavesdropper
advantage of an encryption scheme is zero, then Eve gains no new information by intercepting a single message that Alice
sent to Bob.  We will then use a sequence of games to demonstrate that such a bound does indeed exist.  This thesis is
concerned primarily with the second part of the argument, since the first is generally not readily formalisable.

\section{Important Games}

There are a number of games which will be running examples in the rest of the presentation.  We will describe them
informally here to simplify their presentation when we tackle them formally later on.  These games should also motivate
the necessity of (stateful) oracles and 

\subsection{Indistinguishability Games}

The simplest form of game is one where given two classes $X$ and $Y$ of objects of the same type |T|, the
advantage of an adversary |A : T -> Bool| is
\[
    \abs{\mathbb{P}_{x \in X}[ A x ] - \mathbb{P}_{y \in Y}[ A y ]}.
\]

We say that the classes $X$ and $Y$ are indistinguishable if the advantage is negligible.

A minor variation on this game is when |T| is a function type, and instead of giving it as a parameter we provide it to
the adversary as an oracle:
\[
    \abs{\mathbb{P}_{f \in X}[ A^f ] - \mathbb{P}_{g \in Y}[ A^g ]}.
\]

The adversary then is a parameterless probabilistic computation, which may call the oracle.  As we have said above, this
is equivalent from the point of view of an adversary, but is sometimes easier to reason about.

These games are not very interesting to study directly, but are useful tools for expressing assumptions we may want to
make.  For example, we say that $F$ is a pseudo-random class of functions if it is indistinguishable from the set of all
functions.  This example also illustrates that the classes $X$ and $Y$ need not be disjoint.

\subsection{Eavesdropper Attack}

The eavesdropper attack was already shown in Chapter~\ref{chp:introduction}.  Informally, we can state it as follows.
The challenger possesses a key generation function and an encryption function.  The challenger generates a key $k$, and
takes two messages $(m_0, m_1)$ from the adversary, flips a coin with result $b$, encrypts $m_b$ with $k$, and gives the
result $c$ to the adversary.  The adversary returns a boolean $b'$.  The adversary's advantage is
\[
    \abs{\mathbb{P}[ b = b' ] - \mathbb{P}[ b ]}.
\]

In other words, the advantage is how much better the adversary can do than random chance.

We can regard the eavesdropper attack as a variation on the indistinguishability game where the adversary may choose two
`seed' messages $(m_0, m_1)$ that give rise to the classes $E(m_1)$ and $E(m_2)$, consisting of ciphertexts of $m_0$ and
$m_1$.  The adversary advantage is the advantage the adversary has playing the indistinguishability game between
$X = E(m_0)$ and $Y = E(m_1)$.

\subsection{Chosen-Plaintext Attack}

A slightly stronger attack than the eavesdropper attack is the chosen-plaintext attack, where the adversary has access
to the encryption function.  Typically, this is expressed as the encryption function being registered as an oracle,
though it could simply be given to the adversary directly.  The procedure followed by the challenger and adversary is
otherwise identical to that in the eavesdropper attack.

This attack simulates the situation when Eve intercepts a message, and can then prompt Alice to send a number of known
(encrypted) messages to Bob whilst trying to decipher the original message she intercepted.  This situation arises
naturally in the context of public-key cryptography: since the key to encrypt a message is publicly known, Eve may
encrypt as many messages as she wants.

Two points stand out immediately: a determinsitic encryption scheme cannot be secure against a chosen-plaintext attack,
and no encryption scheme over bitstrings is perfectly secure against a chosen-plaintext attack.

For the first point, suppose $E$ is a deterministic encryption function.  Once the adversary has chosen messages $m_0$
and $m_1$, he can compute $E(m_0)$ and $E(m_1)$ and since $E$ is deterministic, one of these will be equal to the
ciphertext he receives.  The adversary will thus immediately know which message was encoded.

For the second point choose any encryption scheme where the plaintexts and ciphertexts are bitstrings and consider the
following adversary.  Having chosen messages $(m_0, m_1)$ uniformly at random, the adversary receives a ciphertext $c$
and the encryption function $E$.  The adversary computes $E(m_0)$ and $E(m_1)$, and if either is equal to $c$, he knows
what choice the challenger made, since two distinct messages cannot map to the ciphertext.  Otherwise, he flips a coin
and returns the result.

Suppose the challanger chose $m_0$; the other case is symmetric.  The probability distribution $E(m_0)$ is over a subset
of the set of finite bitstrings, and is thus countable.  The probability that the ciphertexts the challenger and
adversary compute are the same is the sum of the squares of the probabilities of each individual ciphertext.  This is
not zero, since the sum of the probabilities of getting each individual ciphertext sums to one, and the probability
space is countable.  It follows that there is some non-zero probability of the adversary computing the same ciphertext.

The adversary can furthermore bring this probability arbitrarily close to 1, since as by querying the oracle $k$ times
per message, the probability becomes $(1-\epsilon)^k$.  It follows that this scheme cannot have perfect security.  In
fact, we see that even concrete security is only possible when the number of queries the adversary can perform is
bounded.  It is in this kind of cases that asymptotic security becomes of key importance, since there do exist many
encryption schemes that are asymptotically secure under assumptions of polynomiality.

\subsection{Chosen-Ciphertext Attack}

An even stronger variant on the eavesdropper attack is when the adversary has access both to the encryption and the
decryption functions used, with the caveat that he may not request that the ciphertext $c$ he got from the challenger be
decrypted.

This extra condition is an additional obstacle when we try to formalise this game, since we cannot inspect the adversary
and guarantee that it does not ask about this ciphertext.  A common approach is to make the deciphering oracle track
whether such a query was made and declare the game `invalid' if it has; the advantage of the adversary is then its
advantage over all valid games.  We hope to be able to improve on this approach by demanding that the adversary prove
(on the type level) that his string is unequal to the ciphertext.

The game described so far is known as IND-CCA2.  There exist other notions, such as when the adversary may only
call the decryption oracle prior to receiving the ciphertext (IND-CCA1).

\section{Example Proofs}

\subsection{ElGamal Encryption}

\subsection{Pseudorandom Functions}

\section{Proof Techinques}

A number of features of the above games are worth emphasising, since their formalisation will be a key part of the
thesis.

\subsection{Bad Events}

Often, two games that we wish to show almost equivalent differ only in some unlikely case.  This is known as a
transition based on a failure event: we isolate a specific case in which the games differ, and show that this case only
happens neglegibly often.  That probability gives us a bound on the distance between the games involved, and since it is
neglegible, the games are still `very close'.

\subsection{Relative Security}

There are certain problems that we expect to be hard, but have not yet proven to be so; the most canonic example is of
course the class of $NP$-complete problems.  In many cases, the security of a scheme can only be proven by assuming that
such a problem really is hard, and working from there.  The system we create should still be useful even in cases like
this, allowing both for the formulation of such an assumption, and for meaningful proofs that rely on it.
