\chapter{The Logic of Games}

%% Chapter structure:
% Explain that we want to syntactically define a logic and why.
% Define this logic.  In particular:
% * Define ==E
% * Define ==eE
% * Define how this extends to adversaries.
% QUESTION: Do we define ==E separately at all, or do we special case it?
% QUESTION: What is the universal property of ==eE w.r.t. uniform?
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

\section{Indistinguishability}

We define an indistinguishability relation on games that encodes the axioms we
impose on our interpretation of distributions.  The following list summarizes
these axioms in English.  For a handling of the implementation in Agda, see
\autoref{chp:code}.
\begin{itemize}
    \item |==E| is an equivalence relation;
    \item |==E| is preserved by |>>=|;
    \item |==E| is closed under the state laws;
    \item |==E| allows for reordering of uniform and state calls;
    \item |==E| allows for merging of uniform calls;
    \item |==E| allows for extension of uniform calls;
    \item |==E| is closed under application of bijections to uniform
    distributions.
\end{itemize}

Note that as is common with equational theories, we only specify what equalities
must hold, but do not specify that any terms may not be indistinguishable.  We
will consider the latter question in more detail in
\autoref{chp:interpretation}.

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

\section{$\epsilon$-Indistinguishability}

There is an $\epsilon$-indistinguishability relationship for every $\epsilon \ge
0$..  Typesetting it is terrible.  It has the following properties:
\begin{itemize}
    \item The relation is reflexive and symmetric.
    \item |==e1D| implies |==e2D| whenever $\epsilon_1 \le \epsilon_2$.
    \item 
\end{itemize}

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
