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

\section{Indistinguishability}

The indistinguishability relation, denoted |==E|, is the least relation on games
that satisfies the following axioms:
\begin{itemize}
    \item |==E| is an equivalence relation;
    \item If |f, g : BitVec n -> CryptoExpr A| such that |forall v -> f v ==E g
    v|, then |Uniform n f ==E Uniform n g|.
    \item If |f, g : ST -> CryptoExpr A| such that |forall v -> f v ==E g
    v|, then |Uniform n f ==E Uniform n g|.
    \item If |f, g : BitVec n -> CryptoExpr A| such that |forall v -> f v ==E g
    v|, then |Uniform n f ==E Uniform n g|.
    \item If 
    \item If both |dx| and |db| do not write to state, or if one writes to state
    and the other does not read from state,
\begin{code}
    dx >>= \ a -> dy >>= \ b -> f a b
\end{code}
    is indistinguishable from
\begin{code}
    dy >>= \ b -> dx >>= \ a -> f a b
\end{code}
    \item If for every |a| and |b|, |f a| is indistinguishable from |f b|, then
    |dx >>= f| is indistinguishable from |f a| for any |a|.
    \item For any bijection |f|, |fmap f (uniform n)| is indistinguishable from
    |uniform n|.
    \item
\begin{code}
    uniform n >>= \ v -> uniform m >>= \ w -> f (v ++ w)
\end{code}
    is indistinguishable from
\begin{code}
    uniform (n+m) >>= f
\end{code}
    \item
\begin{code}
    getState >>= \ s -> getState >>= \ t -> f s t
\end{code}
    is indistinguishable from
\begin{code}
    getState >>= \ s -> f s s
\end{code}
    \item |setState s >> setState t >> ce| is indistinguishable from |setState t
    >> ce|.
    \item |setState s >> getState >>= \ t -> f t| is indistinguishable from
    |setState s >> f s|.
\end{itemize}

Some consequences?  Yes, I'd say:
\begin{itemize}
    \item Any sequence of operations can be reordered into a get, followed by
    uniforms, followed by a set, followed by a return.  
\end{itemize}

\section{$\epsilon$-Indistinguishability}

There is an $\epsilon$-Indistinguishability relationship for every $\epsilon \ge
0$..  Typesetting it is terrible.  It has the following properties:
\begin{itemize}
    \item The relation is reflexive and symmetric.
    \item |==e1D| implies |==e2D| whenever $\epsilon_1 \le \epsilon_2$.
    \item 
\end{itemize}

\section{Tactics}

Now that we have a way of relating games, we want to look at some equivalences
between games that are important for proving things in practice.

\section{Reordering}

In the simplest case, we want to note that certain operations are commutative.
In particular, if a computation does not depend on a random value, we can get
that randomness later:
\begin{code}
uniforminterchange  : (uniformCE n >>= \ a -> ce >>= \ b -> f a b)
                    ==D (ce >>= \ b -> uniformCE n >>= \ a -> f a b)
\end{code}

More interestingly, if there are no |OracleInit| operations involved, we can
reorder operations in general to achieve the following order: |GetAdvState|,
|Uniform|, |OracleCall|, |SetAdvState|.\footnote{Morally, this is true, but
check it's also truly true.}  Additionally, we can use |GetAdvState| and
|SetAdvState| exactly once.  We can similarly combine adjacent uses of
|Uniform|.

This allows us to perform the kind of rewriting we do in the PRF proof where we
unroll the adversary into a sequence of calls to the oracle.  Note that in that
example we can also eliminate |GetAdvState| (since we know the initial state)
and |SetAdvState| (since the state is then projected away).

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
