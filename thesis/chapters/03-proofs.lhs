\chapter{The Logic of Games}

Now that we can represent games, we can start the development of a notion of
indistinguishability between them.  In this chapter, we will introduce a
relation between games and specify the axioms that it must satisfy, giving rise
to a logic of games.  In \autoref{chp:interpretation}, we will show that this
logic is sound by constructing a model of it.

The intuition we want to capture is that two games with outcome |A| are
indistinguishable when the probability of sampling any |a : A| is equal for
both.  Additionally, since this notion is very strong, we also want to relate
games that are not indistinguishable but that differ by at most some $\epsilon$.
The latter is a generalisation of the former, since we get it as a special case
when $\epsilon = 0$.

Note: In the syntactic setting we are working in right now, we can formulate our
conditions with few assumptions on the types involved; in particular, the result
types of games can be anything in |Set|.  However, once we start looking at
interpretations, this becomes problematic: the intuitive relation we will want
to impose on interpretation of games can only be formulated under some
assumptions.  \todo{What can we do about this?}

Note: Also, we will need rational numbers for all this.  Their construction is
not relevant to the problem, so we defer it to \autoref{chp:rationals}.

\section{Properties of Distributions}

Before we introduce the logic, we will prove that the laws we will impose hold
in standard probability theory.

List of notation:
\begin{itemize}
    \item The set of bitstrings of length $n$ is denoted $2^n$.
    \item We regard distributions over a set $A$ as functions $A \to
    \mathbb{R}$ giving the probability of sampling that element.  This is
    possible since all distributions we are interested in are discrete.
    \item We denote the uniform distribution over $2^n$ by $U_n$.
    \item Given a distribution $X$ over a set $A$ and an $A$-indexed family of
    distributions $Y$ over a set $B$, we use $XY$ to denote the combined
    distribution obtained by sampling an $a$ from $X$ and then sampling a $b$
    from $Y_a$.  Equivalently, given a $b \in B$, we define
    \[ XY(b) = \sum_{a \in A} X(a)Y_a(b). \]
    \item Given distributions $X, Y$ over a set $A$, we define the distance
    $\norm{X - Y}$ between these distributions as
    \[
        \norm{X - Y} = \frac{1}{2} \sum{a \in A} \abs{X(a) - Y(a)}
    \]
\end{itemize}

We now look at some consequences of this.

\begin{theorem}
    For every two probability distributions $X, Y$ over some set $A$,
    \[ \norm{X - Y} \le 1. \]
\end{theorem}

\begin{proof}
    Since $X$ and $Y$ are distributions, they take values in $[0, 1]$ and sum to
    $1$.  It follows with the triangle inequality that
    \[
        \frac{1}{2} \sum_{a \in A} \abs{X(a) - Y(a)}
            \le \frac{1}{2} \left(\sum_{a \in A} \abs{X(a)} + \sum_{a \in A}
                \abs{Y(a)}\right)
            \le 1.
    \]
\end{proof}

\begin{theorem}
    Let $X, Y$ be distributions over some set $A$ and let $Z$ be an $A$-indexed
    family of distributions over some set $B$.  Then
    \[ \norm{XZ - YZ} \le \norm{X - Y}. \]
\end{theorem}

\begin{proof}
    Writing out the definition, for any $b \in B$, \[ \abs{XZ(b) - YZ(b)} =
    \abs{\sum_{a \in A} (X(a) - Y(a))(Z_a(b))}.\]  By the triangle inequality,
    \[ \sum_{b \in B} \abs{XZ(b) - YZ(b)}
        \le \sum_{b \in B}\sum_{a \in A} \abs{X(a) - Y(a)}\abs{Z_a(b)}. \]
    Since each $Z_a$ is a probability distribution, $\sum_{b \in B}\abs{Z_a(b)}
    = 1$, hence
    \[ \sum_{b \in B} \abs{XZ(b) - YZ(b)}
        \le \sum_{a \in A} \abs{X(a) - Y(a)}. \]
\end{proof}

\begin{theorem}
    Let $X$ be a distribution over some set $A$ and let $Y, Z$ be $A$-indexed
    families of distributions over some set $B$.  If there is a $g : A \to
    \mathbb{R}$ such that for every $a \in A$,
    \[ \norm{Y_a - Z_a} \le g(a) \]
    then
    \[ \norm{XY - XZ} \le \sum_{a \in A} X(a)g(a). \]
\end{theorem}

\begin{proof}
    Writing out the definition, for any $b \in B$, \[ \abs{XY(b) - XZ(b) } =
    \abs{\sum_{a \in A} X(a)(Y_a(b) - Z_a(b))}. \]  As above, by the triangle
    inequality we get
    \[ \sum_{b \in B} \abs{XY(b) - XZ(b)} \le
        \sum_{b \in B}\sum_{a \in A} \abs{X(a)}\abs{Y_a(b) - Z_a(b)} \]
    and now using the assumption and the fact $X$ is a distribution we get
    \[ \sum_{b \in B} \abs{XY(b) - XZ(b)} \le
        \sum_{a \in A} X(a)g(a). \]
\end{proof}

This has two useful consequences.

\begin{corollary}
    Let $X$ be a distribution over some set $A$ and let $Y, Z$ be $A$-indexed
    families of distributions over some set $B$.  If there is an $\epsilon$ such
    that $\norm{Y_a - Z_a} \le \epsilon$ for every $a \in A$, then
    \[ \norm{XY - XZ} \le \epsilon. \]
\end{corollary}

\begin{corollary}
    Let $n \in \mathbb{N}$ and let $X, Y$ be $2^n$-indexed families of
    probability distributions over some type $A$.  Then if there is a $g : 2^n \to
    \mathbb{R}$ such that $\norm{X_v - Y_v} \le g(v)$, then
    \[
        \norm{U_nX - U_nY} \le \frac{1}{2^n} \sum_{v \in 2^n} g(v).
    \]
\end{corollary}

\section{$\epsilon$-Indistinguishability}
\label{sec:epsilon-indistinguishability}

We will now define a family of relations |==eE| that represents that two games,
seen as probability distributions, are at a distance of at most $\epsilon$,
where $\epsilon$ is a non-negative rational.  For now, this is a purely
syntactic construction; we will look at a semantical interpretation in
\autoref{chp:interpretation}.

The full axiomatisation of |==eE| is available in the Agda code.  However, since
it involves a considerable number of technical details that are not interesting
from a logical perspective, we will present the axioms here informally.  We say
that two games |G| and |H| with the same result type are
$\epsilon$-indistinguishable iff |G ==eE H| holds.  We say that two |A|-indexed
families of games |f| and |g| are $h$-indistinguishable if for every |a : A|, |f
a| and |g a| are $h(a)$-indistinguishable.  If $h$ is a constant function equal
to $\epsilon$, we say |f| and |g| are $\epsilon$-indistinguishable.

When we say |==eE| is closed under some substitution of actions $A1, A2, \ldots,
An$
for actions $B1, B2, \ldots, Bn$, we mean that for any continuation |cont| there
exists a continuation |cont'| such that the games
%{
%format A1 = "A_1"
%format A2 = "A_2"
%format An = "A_n"
%format a1 = "a_1"
%format a2 = "a_2"
%format an = "a_n"
%format B1 = "B_1"
%format B2 = "B_2"
%format Bn = "B_n"
%format b1 = "b_1"
%format b2 = "b_2"
%format bn = "b_n"
%format ldots = "\ldots"
\begin{code}
A1 >>= \ a1 -> A2 >>= \ a2 -> ldots -> An >>= \ an -> cont a1 a2 ldots an
\end{code}
and
\begin{code}
B1 >>= \ a1 -> B2 >>= \ a2 -> ldots -> Bn >>= \ an -> cont' a1 a2 ldots an
\end{code}
%}
are $\epsilon$-indistinguishable.  The definition of |cont'| is typically clear
from the context.

The axioms of $\epsilon$-indistinguishability are as follows:
\begin{itemize}
    \item |==eE| is reflexive and symmetric.
    \item If |G ==e1E H| and |H ==e2E I| then |G ==eeE I|.
    \item Every two games are $1$-indistinguishable.
    \item If |G ==eE H| and |f| is a family of games, then |G >>= f ==eE H
    >>= f|.
    \item If |G| is a game with result type |A| and |f| and |g| are |A|-indexed
    families of games that are $\epsilon$-indistinguishable, then |G >>= f ==eE
    G >>= h|.
    \item |==eE| is closed under the state laws;
    \item |==eE| is closed under the reordering of |uniform| and |getState|
    operations;
    \item |==eE| is closed under the reordering of |uniform| and |setState|
    operations;
    \item |==eE| is closed under the insertion of |uniform| and |getState|
    operations;
    \item |==eE| is closed under replacing consecutive occurences of |uniform n|
    and |uniform m| by |uniform (n+m)|.
    \item |==eE| is closed under application of bijections to uniform
    distributions.
    \item If two $2^n$-indexed families of games |f| and |g| are
    $h$-indistinguishable, then |uniform >>= f| and  |uniform >>= g| are
    $\left(\sum_{v : 2^n} h(v)\right)$-indistinguishable.
  \end{itemize}

Note that as is common with equational theories, we only specify what equalities
must hold, but do not specify that any terms may not be
$\epsilon$-indistinguishable.  We will consider the latter question in more
detail in \autoref{chp:interpretation}.

A special case of this relation arises when $\epsilon = 0$.  We denote this
relation |==E| and say that two games |a| and |b| satisfying |a ==E b| are
indistinguishable, dropping the $\epsilon$.  The |==E| relation is of key
importance to the further development since it is a congruence: this means that
we can replace all occurences of a subgame with an indistinguishable subgame
even if we do not know how many occurences there are, and the resulting game
will be indistinguishable from what we started.  This makes reasoning
considerably easier than in the case of $\epsilon$-indistinguishability, where
the number of occurences must be bounded for the result to be meaningful.

The following simple theorem is often useful in practice.

\begin{theorem}
    |==e1E| is a subrelation of |==e2E| if $\epsilon_1 \le \epsilon_2$.
\end{theorem}

\begin{proof}
    The proof is by induction on the derivation of |a ==e1E b|.  All the cases
    are trivial: for example, in the last axiom, we can take $h'(v) = h(v) +
    \epsilon_2 - \epsilon_1$.  By induction, $f$ and $g$ are
    $h'$-indistinguishable and the desired result follows.
\end{proof}

An important result we can obtain using this logic is that every game can be
rewritten into a canonical form.  This is a first step to being able to perform
the kind of rewriting steps we required in \autoref{sec:intro-prf}.

\begin{theorem}
    Every |ce : CryptoExpr ST A| is indistinguishable from some |CryptoExpr ST
    A| of the form
    \begin{code}
        GetState \ st ->
        Uniform (f st) \ v ->
        SetState (g st v) \ _ ->
        Return (h st v)
    \end{code}
\end{theorem}

Note that we do not assume that the state type |ST| is finite or has decidable
equality.  Given such an assumption, we could reverse the order of the
|GetState| and |SetState| call.

\begin{proof}
    The full proof is in the Agda code, and proceeds in two steps: we first
    construct |f|, |g|, and |h| and then show indistinguishability.  In all
    cases, the construction is by recursion on the structure of |ce|.

    The key idea of the proof is to explicitly pass around the current state
    |st| and, in the case of |g| and |h|, a sufficiently long bitvector of
    random bits.  Since |f| does not have access to such a bitvector (being the
    function that determines how much randomness we require), it must enumerate
    all bitvectors of the right length when the recursion is on a |Uniform|
    constructor.  This makes explicitly computing this canonical form
    impractical, but is not an obstacle to reasoning with it.

    The main difficulty in the proof is showing that the vector |v| has
    sufficient random bits.  This is not a conceptual problem; it is just a
    technicality caused by the fact that not every branch of a |Uniform|
    constructor must use the same number of random bits.  This leads to the
    following problem: the |Uniform n cont| case of |g| requires that |v| have
    length |n + k|, where |k| is the maximum number of random bits |cont| may
    use.
\end{proof}

\section{Result-Indistinguishability}

It is tempting to assume that the notion of $\epsilon$-indistinguishability we
have just defined represents $\epsilon$-indistinguishability as we used the term
in \autoref{chp:introduction}.  Unfortunately, the situation is somewhat more
nuanced.

In \autoref{chp:introduction}, we considered computations to be
indistinguishable even if they had different effects on the state of the
adversary.   We did not have this luxury when defining the notion of
$\epsilon$-indistinguishability above, since we wanted |==eE| to be closed under
bind.  Without this, the |==eE| relation would not be composable, and we would
not be able to show that replacing of indistinguishables in the middle of a game
gives indistinguishable results.

When it comes to bounding the advantage of the adversary, however, we do
\emph{not} want to distinguish outcomes based on the state of the adversary: two
adversaries that both win the game with probability 0.5 are equivalent for our
purposes, even if we can distinguish between them based on the effect they have
on the state.  As such, we want a weaker notion of indistinguishable which we
will call ($\epsilon$-)result-indistinguishability.  This is the notion which
will be used for reasoning about complete games, while
$\epsilon$-indistinguishability will be used for reasoning about their parts.

As with $\epsilon$-indistinguishability, we specify the axioms of
$\epsilon$-result-indistinguishability, denoted |==eR|, in Agda and provide an
informal overview of these axioms here.

\section{Indistinguishability with Oracles}

In order to speak of indistinguishability with oracles we need to keep track of
the oracle implementation.  Let's say we have a type |GameImpl OST AST A| that
consists of an oracle implementation with state |OST| and a |CryptoExpr AST A|.
We have seen how this can be glued together into a single |CryptoExpr (AST *
OST) A|.

This gives rise to a |==OE| relation between |GameImpl|s.  We could just reason
about it directly, but it is convenient to add some assumptions.

\begin{theorem}
    Changing the oracle implementation to one that is fully indistinguishable
    preserves indistinguishability.
\end{theorem}

\begin{corollary}
    Every |GameImpl| is indistinguishable from one where the oracle
    implementations are in canonic form.
\end{corollary}

\begin{theorem}
    Something something canonic form.
\end{theorem}

\begin{theorem}
    If the number of oracle calls is bounded by $k$
\end{theorem}


\section{Identical Until Bad}

This is something I still need to work on.  Given two games and some predicate
on their outcome (on the state?), and a proof that they give identical results
if the bad thing doesn't happen, we can prove that their difference is bounded
by the probability of the bad event.

Problems and questions:
\begin{itemize}
    \item Even if we can prove this, the number of claims the user must show is
    pretty large.  In particular, it seems very hard to argue that the games are
    identical without the bad event; ``bad even didn't happen'' just isn't a
    very strong assumption to work with.
    \item We need a completely different argument here if the oracle changes
    rather than if the game changes.  Really, this becomes a new principle in
    this setting.  Pity.
    \item We could add an extra |MaybeT| on top of everything and add an |Abort|
    command to bail out.  We can then compute the probability\ldots I guess?
    But is the adversary allowed to abort, or is it the special power of the
    oracle?  It seems like certain bad events (e.g. the adversary breaking the hash
    function) are modelled this way but not explicitly detectable.
    \item Suppose we've avoided all the above.  What would a proof look like?  I
    guess we can argue that certain states are equivalent, so the differences in
    probability are all focused in the area which we have already bounded?
\end{itemize}

\section{Security Assumptions and Polynomial Adversaries}
\label{sec:security-assumptions}

Sometimes we want to assume that some property holds: for example, that our hash
function is hard to break.  How does this fit into the system?

I guess typically this is just an assumption that two games are similar, but how
can this be phrased well without reference to the evaluation?

\section{Asymptotic Indistinguishability}
\label{sec:asymptotic-indistinguishability}

\section{Example: PRF, Formalised}

It is enlightening (?) to see how the above steps can be used to show that the
game described can be formalised.
