\chapter{The Logic of Games}

%% Chapter structure:
% Explain that we want to syntactically define a logic and why.
% Define this logic.  In particular:
% * Define ==eE
% QUESTION: What is the universal property of ==eE w.r.t. uniform?
% * Define how this extends to adversaries.
% * Define ==E as a special case
% Motivate the ==eE equalities 
% Show some consequences of this logic.
% * Canonic form theorem (Get/Uniform/Set)
% * Cannoic form with oracle theorem (Get/Uniform/Oracle*/Set)
% * Identical until bad theorem
% QUESTION: How do we formulate identical until bad?
% Work out PRF example in this system.

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

We define a relation |==eE| between games indexed by a non-negative rational
$\epsilon$.  The following properties must hold of this relation:
\begin{itemize}
    \item |==eE| is reflexive and symmetric.
    \item If |a ==e1E b| and |b ==e2E c| then |a ==eeE c|.
    \item |==1E| relates every two games;
    \item |==eE| is preserved by |>>=|;
    \item |==eE| is closed under the state laws;
    \item |==eE| is closed under the reordering of uniform and state operations;
    \item |==eE| is closed under the insertion of uniform and state read
    operations;
    \item |==eE| is closed under the merging of uniform operations;
    \item |==eE| is closed under application of bijections to uniform
    distributions.
    \item |uniform >>= a ==eE uniform >>= b| if we show |a v ==gvE b v| for every
    |v : BitVec n| and $\epsilon \ge \frac{1}{2^n}\sum_v g(v)$.
\end{itemize}

Note that as is common with equational theories, we only specify what equalities
must hold, but do not specify that any terms may not be indistinguishable.  We
will consider the latter question in more detail in
\autoref{chp:interpretation}.

A special case of this relation arises when $\epsilon = 0$.  We denote this
relation |==E|.

There are a number of interesting properties worth mentioning.

\begin{theorem}
    |==E| is an equivalence relation.
\end{theorem}

\begin{theorem}
    |==e1E| is a subrelation of |==e2E| if $\epsilon_1 \le \epsilon_2$.
\end{theorem}

We will now look at some consequences of this equational theory.

\begin{theorem}
    Every |ce : CryptoExpr ST A| is equivalent to a |CryptoExpr ST A| of the
    form
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

The proof is in the code.

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


\section{Result-Indistinguishability}

When we are judging whether an adversary has really managed to gain an advantage
in the game, we want to see whether the result of the game is indistinguishable
from a coin flip, not whether the accompanying state changes differ.  Moreover,
we are interested in the result only starting from a particular state.  This is
especially relevant for the oracle, whose state is opaque to the challenger and
adversary.

TODO: Write out a logic for reasoning about this.

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

\section{Security Assumptions}

Sometimes we want to assume that some property holds: for example, that our hash
function is hard to break.  How does this fit into the system?

I guess typically this is just an assumption that two games are similar, but how
can this be phrased well without reference to the evaluation?

\section{Example: PRF, Formalised}

It is enlightening (?) to see how the above steps can be used to show that the
game described can be formalised.
