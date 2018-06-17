\chapter{Proof Techniques}

Now that we have a way of relating games, we want to look at some equivalences
between games that are important for proving things in practice.

\section{Reordering}

In the simplest case, we want to note that certain operations are commutative.
In particular, if a computation does not depend on a random value, we can get
that randomness later:
\begin{code}
uniforminterchange  : (uniformCE n >>= \ a -> ce >>= \ b -> f a b)
                    ==D (ce >>= \b -> uniformCE n >>= \ a -> f a b)
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

