\chapter{The Logic of Games}
\label{chp:proofs}

Now that we can represent games, we can define a notion of indistinguishability
to relate them to each other.  In this chapter, we will continue with our
syntactic approach and define indistinguishability in a purely formal manner.

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
\label{sec:proofs-dists}

Since we are interested in modelling the (equational) logic of probability
distributions, we will start by looking at the laws that these distributions
satisfy in classical mathematics.  Fortunately, we are only interested in
discrete probability distributions with finite support.  We can thus model a
probability distribution $X$ over a set $A$ as a function $A \to \mathbb{R}$
giving the probability of sampling $a \in A$ from $X$.

To start, a little notation: we will use $2^n$ to denote the bitvectors of
length $n$, and $U_n$ to denote the uniform distribution over $2^n$.  The
Dirac delta distribution that gives an element $a \in A$ probability 1 is
denoted $1_a$.  Given a distribution $X$ over $A$ and an $A$-indexed family of
distributions $Y$ over $B$, we denote the composite distribution obtained by
sampling $a$ from $X$ and then $b$ from $Y_a$ as $XY$, defined by
\[ XY(b) = \sum_{a \in A} X(a)Y_a(b). \]
Finally, given distributions $X$ and $Y$ over the same set $A$, we define the
distance between them as follows:
\[ \norm{X-Y} = \frac{1}{2} \sum_{a \in A} \abs{X(a) - Y(a)}. \]

The following theorem motivates the $\frac{1}{2}$ in the definition of the
distance:
\begin{theorem}
    For every two probability distributions $X, Y$ over some set $A$,
    \[ \norm{X - Y} \le 1. \]
\end{theorem}

\begin{proof}
    Since $X$ and $Y$ are distributions, they take values in $[0, 1]$ and sum to
    $1$.  It follows by the triangle inequality that
    \[
        \frac{1}{2} \sum_{a \in A} \abs{X(a) - Y(a)}
            \le \frac{1}{2} \left(\sum_{a \in A} \abs{X(a)} + \sum_{a \in A}
                \abs{Y(a)}\right)
            \le 1.
    \]
\end{proof}

The composition of distributions operation corresponds to the monadic bind
operation.  The monad, in this case, sends a set $A$ to the set of all
probability distributions over $A$, and the unit sends an element $a \in A$ to
the Dirac delta distribution $1_a$.

The logic of this monadic bind is of particular interest to is, since we are
interested in knowing how much changing a single step of a game will influence
the game as a whole.  The following results tell us that the effect of such a
substitution is at most linear in the number of occurences.

We use $A$ and $B$ to denote arbitrary sets in the following.

\begin{theorem}
    Let $X, Y$ be distributions over $A$ and let $Z$ be an $A$-indexed
    family of distributions over $B$.  Then
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
    Let $X$ be a distribution over $A$ and let $Y, Z$ be $A$-indexed
    families of distributions over $B$.  Then
    \[ \norm{XY - XZ} \le \sum_{a \in A} X(a)\norm{Y_a - Z_a}. \]
\end{theorem}

\begin{proof}
    Writing out the definition, for any $b \in B$, \[ \abs{XY(b) - XZ(b) } =
    \abs{\sum_{a \in A} X(a)(Y_a(b) - Z_a(b))}. \]  As above, by the triangle
    inequality we get
    \[ \sum_{b \in B} \abs{XY(b) - XZ(b)} \le
        \sum_{b \in B}\sum_{a \in A} \abs{X(a)}\abs{Y_a(b) - Z_a(b)} \]
    and now using the non-negativity of $X$ we get
    \[ \sum_{b \in B} \abs{XY(b) - XZ(b)} \le
        \sum_{a \in A} X(a)\left(\sum_{b \in B}\abs{Y_a(b) - Z_a(b)}\right)
        = \sum_{a \in A} X(a)\norm{Y_a - Z_a} \]
\end{proof}

This has two useful consequences.

\begin{corollary}
    Let $X$ be a distribution over $A$ and let $Y, Z$ be $A$-indexed families of
    distributions over $B$.  If there is an $\epsilon$ such that $\norm{Y_a -
    Z_a} \le \epsilon$ for every $a \in A$, then
    \[ \norm{XY - XZ} \le \epsilon. \]
\end{corollary}

\begin{corollary}
    Let $n \in \mathbb{N}$ and let $X, Y$ be $2^n$-indexed families of
    probability distributions over $A$.  Then
    \[
        \norm{U_nX - U_nY} \le \frac{1}{2^n} \sum_{v \in 2^n} \norm{X_v - Y_v}.
    \]
\end{corollary}

\section{$\epsilon$-Relations}

A recurring theme in our constructions is a relation indexed by a non-negative
rational $\epsilon$, and  that is an equivalence relation for $\epsilon = 0$,
and that is weakenable.

\begin{definition}
    $R_\epsilon$ is an \emph{$\epsilon$-relation} on $A$ if
    \begin{itemize}
        \item For every $a \in A$, $R_\epsilon(a, a)$;
        \item For every $a, b \in A$, if $R_\epsilon(a, b)$ then $R_\epsilon(b, a)$;
        \item For every $a, b, c \in A$, if $R_{\epsilon_1}(a, b)$ and
        $R_{\epsilon_2}(b, c)$ then $R_{\epsilon_1 + \epsilon_2}(a, c)$.
        \item For every $a, b \in A$, if $R_{\epsilon_1}(a, b)$ and $\epsilon_1 \le
        \epsilon_2$ then $R_{\epsilon_2}(a, b)$.
        \item For every $a, b \in A$, $R_1(a, b)$.
    \end{itemize}
\end{definition}

Functorial version: closed under fmap?
Monadic version: closed under bind?

\begin{theorem}
    The norm defined above gives rise to an $\epsilon$-relation.
\end{theorem}

\section{$\epsilon$-Indistinguishability}
\label{sec:epsilon-indistinguishability}

\todo{This kind of family of relations is a common theme here; maybe give it a
name?}
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
When we say |==eE| is closed under some substitution of actions $A_1, A_2, \ldots,
A_n$ for actions $B_1, B_2, \ldots, B_n$, we mean that for any continuation |cont|
there exists a continuation |cont'| such that the games
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
    \item If |f| and |g| are families of games indexed by the result type |R| of
    a primitive command |c|\footnote{That is, |GetState|, |SetState| or
    |Uniform|} and |f r ==eE g r| for every |r : R| then |c f ==eE c g|.
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

In \autoref{sec:proofs-dists} we discussed the importance of the fact that the
distance between probability distributions remains bounded under monadic
binding.  These properties can be proved from our axioms.

\begin{theorem}
    If |G| is a game with result type |A| and |f| and |g| are |A|-indexed
    families of games that are $\epsilon$-indistinguishable, then |G >>= f ==eE
    G >>= h|.
\end{theorem}

\begin{proof}
    This is a straightforward recursion on the structure of |G|.
\end{proof}

\begin{theorem}
    If |G ==eE H| and |f| is a family of games, then |G >>= f ==eE H >>= f|.
\end{theorem}

\begin{proof}
    This proof goes by induction on the derivation of |G ==eE H|.  There are
    many cases, but they are all straightforward.
\end{proof}

An important result we can obtain using this logic is that every game can be
rewritten into a canonical form.  This is a first step to being able to perform
the kind of rewriting steps we required in \autoref{sec:intro-prf}.  We denote
this form as $\epsilon$-canonical form.\footnote{A possible source of confusion
is that the normal form does not depend on the value of $\epsilon$: rather, this
is the $\epsilon$-canonical form as it is canonical with respect to
$\epsilon$-indistinguishability, as opposed to the other notions of
indistinguishability introduced later.}

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
    length |n+k|, where |k| is the maximum number of random bits |cont| may
    use.  If |v| has this length, then we can split it into vectors |l| and |r|
    of length |n| and |k| respectively, and recurse on |cont l| using |r| as our
    vector of random bits.  However, suppose now that |cont l| is again of the
    form |Uniform n' cont'|.  To split |r|, we require that it have length
    |n'+k'|.  But |r| has length |k|, which is a maximum of a list, and thus not
    of this form at all.

    Careful manipulation of indices can resolve these issues, but they
    considerably complicate this otherwise fairly straightforward proof.
\end{proof}

\section{Result-Indistinguishability}

It is tempting to assume that the notion of $\epsilon$-indistinguishability we
have just defined represents $\epsilon$-indistinguishability as we used the term
in \autoref{chp:introduction}.  Unfortunately, the situation is somewhat more
nuanced.

In \autoref{chp:introduction}, we considered games to be indistinguishable even
if they had different effects on the state of the adversary.   We did not have
this luxury when defining the notion of $\epsilon$-indistinguishability above,
since we wanted |==eE| to be closed under bind.  Without this, the |==eE|
relation would not be a congruence.

When it comes to bounding the advantage of the adversary, however, we do
\emph{not} want to distinguish outcomes based on the state of the adversary: two
adversaries that both win the game with probability 0.5 are equivalent for our
purposes, even if we can distinguish between them based on the effect they have
on the state.  As such, we want a weaker notion of indistinguishability which we
will call $(\epsilon, st)$-indistinguishability or result-indistinguishability.
This is the notion which will be used for reasoning about complete games, while
$\epsilon$-indistinguishability will be used for reasoning about their parts.
The $st$ refers to the initial value of the state.

As with $\epsilon$-indistinguishability, we specify the axioms of
$(\epsilon, st)$-indistinguishability, denoted |==eR|, in Agda and
provide an informal overview of these axioms here.  The relation |==eR| is
indexed by |Q * ST| pairs and satisfies the following axioms:
\begin{itemize}
    \item |==eE| is a subrelation of |==eR| for each |st|.
    \item |==eR| is symmetric.
    \item If |G ==e1R H| and |H ==e2R I| then |G ==eeR I|.
    \item Every two games are $(1, st)$-indistinguishable.
    \item If |G ==eR H| and |f| is an |A|-indexed family of games such that for
    each |a : A|, |f a| does not use state, then |G >>= f ==eR H >>= f|.
    \item If |G| is a game with result type |A| that does not use state and |f|
    and |g| are |A|-indexed families of games that are
    $(\epsilon, st)$-indistinguishable, then |G >>= f ==eR G >>= h|.
    \item |getState >>= cont| is $(\epsilon, st)$-indistinguishable from |cont
    st|.
    \item |ce >>= \ a -> setState (f a) >> return (g a)| is $(\epsilon,
    st)$-indistinguishable from |fmap g ce| for any |f| and |g|.
    \item If two $2^n$-indexed families of games |f| and |g| are
    $(h, st)$-indistinguishable, then |uniform >>= f| and  |uniform >>= g| are
    $\left(\sum_{v : 2^n} h(v), st\right)$-indistinguishable.
\end{itemize}

As before, we denote the special case of $(0, st)$-indistinguishability by
$st$-indistinguishability.  Important to note is the difference between the
|getState| and |setState| axioms.  In the former case, we know the state to be
|st|, and so we do not need to restrict whether |cont| may or may not use state.
In |setState|, on the other hand, we cannot allow an arbitrary continuation, but
we can allow arbitrary game to precede the |setState| class, since the
difference in state cannot later be observed.  The |setState| case can be
generalised to the following theorem, which will prove useful later.

\begin{theorem}
    \label{thm:post-insert}
    For any game |X| and family of games |Y|, |fmap g X| is result-indistinguishable
    from |X >>= \ a -> Y a >> return (g a)|.
\end{theorem}

\begin{proof}
    We can assume that |Y a| is in $\epsilon$-canonical form.  Note that the
    insertion of |getState| and |uniform| operations gives games that are
    $\epsilon$-indistinguishable.  It follows that |fmap g X| is
    indistinguishable from
    \begin{code}
        X >>= \ a ->
        getState >>= \ st ->
        uniform (f a st) >>= \ v ->
        return (g a)
    \end{code}
    By the monad laws, we can reassociate this to
    \begin{code}
        (X >>= \ a ->
        getState >>= \ st ->
        uniform (f a st) >>= \ v ->
        return (a , st , v)) >>= \ pr
        return (g dollar fst dollar snd pr)
    \end{code}

    We can now use the |setState| axiom to conclude this is
    result-indistinguishable from
    \begin{code}
        (X >>= \ a ->
        getState >>= \ st ->
        uniform (f a st) >>= \ v ->
        return (a , st , v)) >>= \ pr
        setState (Y dollar fst dollar fst pr) >>= \ _ ->
        return (g dollar fst dollar snd pr)
    \end{code}

    By the monad laws, this is equal to the desired result.
\end{proof}

Games considered up to result-indistinguishability have an even stronger
canonical form, which we call the $(\epsilon, st)$-canonical form.

\begin{theorem}
    Every game |ce : CryptoExpr ST A| is result-indistinguishable from a game of
    the form
    \begin{code}
        Uniform n \ v -> Return (f v)
    \end{code}
\end{theorem}

\begin{proof}
    It suffices to show that every $\epsilon$-canonical form is
    result-indistinguishable from an $(\epsilon, st)$-canonical form.
    By the |getState| axiom for result-indistinguishability, it is
    $st$-indistinguishable from
    \begin{code}
        Uniform (f' st) \ v ->
        SetState (g' st v) \ _ ->
        Return (h' st v)
    \end{code}

    By the |setState| axiom and using the fact that |Uniform| and |Return| are
    stateless, we see thisis $st$-indistinguishable from
    \begin{code}
        Uniform (f' st) \ v ->
        Return (h' st v)
    \end{code}

    Since |st| is fixed, we can take |n = f' st| and |f = h' st|, giving the
    desired result.
\end{proof}

\begin{corollary}
    For every game |ce : CryptoExpr ST Bool|, there is some probability |p| such
    that |ce| is result-indistinguishable from the
    Bernoulli distribution |Bp : CryptoExpr ST Bool| with parameter |p|.
\end{corollary}

\begin{theorem}
    \label{thm:finite-support}
    Let |A| be a type with decidable equality.  For any game |X : CryptoExpr ST
    A|, given |st : ST|, there is a list |f st : List A| representing the
    support of |X|, in the sense that the following game is
    result-indistinguishable from |return true|:
    \begin{code}
        getState >>= \ st ->
        X >>= \ a ->
        return (elem a (f st))
    \end{code}
\end{theorem}

\section{Indistinguishability with Oracles}

In order to reason about games involving oracles, we want to extend the notions
of $\epsilon$-indistinguishability and $(\epsilon, st)$-indistinguishability to
pairs of games involving oracles and oracle definitions for these games.  Since
we can compile such a pair into a game not involving oracles, we can lift these
notions directly, which we shall do.  We will then look at the consequences of
this definition, and the rewrite rules we can derive.

We will assume that the types |OracleInit|, |OracleArg|, |OracleResult|, and
|OST| all have decidable equality.  Finding where these restrictions can be
relaxed would be a good candidate for further work in this area.

Formally speaking, given |ce| and |cf| of type |OracleExpr AST A| and |impl| and
|jmpl| of type |Oracle OST|, we say that |(ce , impl) ==eOE (cf , jmpl)| iff |eval
ce impl ==eE eval cf jmpl|.  We will write |ce ==eOEimpl cf| if |impl| is the
same on both sides.  We will also write |impl ==eE jmpl|  iff for every |i :
OracleInit|, |Init impl i ==eE Init jmpl i|  and for every |a : OracleArg|,
|Call impl arg ==eE Call jmpl arg|.  The definitions for |==eOR| and |==eR| on
oracle implementations are analogous.

The following simple results will make our life easier going forward:
\begin{theorem}
    If |impl ==E jmpl| and |ce : OracleExpr AST A|, then |(ce , impl) ==OE (ce ,
    jmpl)|.  The same result does not hold for $\epsilon$-indistinguishability,
    nor for result-indistinguishability.
\end{theorem}

\begin{proof}
    This is easy to show by induction on the structure of |ce|.  The |GetState|,
    |SetState|, and |Uniform| cases hold by reflixivity, while |impl ==E jmpl|
    gives us the |InitOracle| and |CallOracle| cases.

    The failure for $\epsilon$-indistinguishability can be seen in the following
    game: let $0 < \epsilon < 1$ and consider an oracle that returns |true| with
    probability $\epsilon$, and a game which calls the oracle $n$ times and
    return |true| iff any oracle call returned |true|.  The probability that the
    game returns true is $1 - (1 - \epsilon)^n$, which goes to $1$ as $n$ goes
    to infinity and so is not bounded by $\epsilon$.

    The failure for result-indistinguishability can be seen as follows: every
    oracle implementation is result-indistinguishable from one where the
    initialisation is |return tt|.  This would thus imply that every game
    involving an oracle is result-indistinguishable to one where the oracle is
    not initialised, which is clealy not the case.
\end{proof}

Since every game is indistinguishable from a game in $\epsilon$-canonical form,
it follows that every oracle implementation |impl| is indistinguishable from an
implementation |impl'| such that each |Init impl' i| and |Call impl' arg| are in
$\epsilon$-canonical form.  Going forward, we will assume all our oracle
implementations are of this form unless we specify otherwise.

We would now like to find an $(\epsilon, st)$-canonical form for games that make
use of oracles.  We start by studying the reordering and insertion rules of
these games.

\begin{theorem}
    Games that do not make use of the oracle can be reordered with games that do
    not make use of the state, in the following sense: for any game |X| that
    does not make use of the oracle, any game |Y| that does not make use of the
    state, and any continuation |cont|, the following games are
    indistinguishable:
    \begin{code}
        X >>= \ a ->  Y >>= \ b ->  cont a b
        Y >>= \ b ->  X >>= \ a ->  cont a b
    \end{code}
\end{theorem}

\begin{proof}
    The proof consists of several proofs by induction.  First, we show that
    every |GetState|, |SetState|, and |Uniform| operation can be reordered with
    an |OracleInit|, |OracleCall|, or |Uniform| operation, in the same sense as
    this theorem.  We can then show, by induction on |X|, that we can reorder
    |X| with the first operation on |Y|.  By induction on |Y|, we iterate this
    construction to show that |X| and |Y| can be fully reordered.

    The key insight is that the |SetState| and |GetState| operations of the game
    and of the oracle can be reordered, since they always act on distinct
    components of the state tuple.
\end{proof}

\begin{theorem}
    Up to oracle result-indistinguishability, any game |X| can be extended with
    any family of games |Y|, in the sense that |fmap g X| is
    result-indistinguishable from |X >>= \ a -> Y a >> return (g a)|.
\end{theorem}

\begin{proof}
    Note that this is just a restatement of \autoref{thm:post-insert} in the oracle
    setting, and follows directly from that theorem.
\end{proof}

We conjecture that the canonical form results we obtained earlier can be
generalised to the oracle case.  Unfortunately, these results are much harder to
state than the non-oracle equivalents, since we must allow for the alternation
of an arbitrary number of |OracleInit| and |OracleCall| operations.  In
practice, we will usually wish to assume the order is specified by some proof
term such as |BoundedOracleUse| from \autoref{sec:games-constraints}.  Given
such a proof term, we expect to be able to compute the canonical form.  However,
due to time constraints we have not been able to show this in Agda.

\section{Generalised Security}
\label{sec:security-assumptions}
\label{sec:asymptotic-indistinguishability}

As we have already remarked in \autoref{sec:intro-weaker}, there are many cases
when we want to show security only against adversaries that are restricted in
the resources they may use.  The prime example of this is a restriction to
adversaries that run in polynomial time.  Restricting the problem in this way
allows us to use assumptions about what a polynomial-time algorithm cannot do.
This allows us to reason about the security of systems that depend on problems
like integer factorisation being hard; without such an assumption, since integer
factorisation can be performed in Agda, we cannot rule out that the adversary
performs the factorisation and thereby defeats our security scheme.

Within our system, we cannot create a type of polynomial-time adversaries, and
so we cannot allow a game to restrict its inputs to be polynomial-time
adversaries.  However, we can still achieve the desired effect by assuming that
certain operations cannot be performed by any adversary.  We do this by assuming
that certain games are unwinnable, using the generalised notion of games
described in \autoref{sec:intro-general-games}.

For example, let us consider the discrete logarithm problem.  Given a cyclic
group $G$ and a generator $g$, the Decisional Diffie-Hellman assumption states
that it is hard to distinguish the triple $(g^a, g^b, g^c)$ with $a, b, c$ all
uniformly random (with $0 \le a < |G|$) from $(g^a, g^b, g^{ab})$, with $a, b$
uniformly random.  We can phrase this as follows: let |G| be the uniform
distribution over $G$.  Then there is some $\epsilon$ such that the following
two games are $(\epsilon, st)$-indistinguishable for any adversary |adv|:
\begin{code}
do
    a <- G
    b <- G
    c <- G
    adv (pow g a , pow g b , pow g c)

do
    a <- G
    b <- G
    adv (pow g a , pow g b , pow g (mul a b))
\end{code}

We can then use this assumption to replace the usage of |pow g (mul a b)| in a
proof with |pow g c|.  This is a key step in proving the security of the ElGamal
encryption scheme, for example.\todo{cite Shoup}  By introducing this assumption
we show that no adversary can find |a| given |pow g a|, since otherwise they
could take |pow (pow g b) a| and compare it to the third component of the tuple.

A significant downside to this approach is that our assumptions must all be
phrased as decision problems.\todo{Why is this bad?}

Another issue with this approach is that while this allows us to reason about an
arbitrary adversary as if it satisfied our assumptions, it does not restrict the
class of adversaries that we may use as a counterexample: it is thus necessary
to check the validity of any constructed adversaries by hand.

Finally, an assumption of this kind only states that such an $\epsilon$ exists,
without any bounds on the size of this $\epsilon$.  This is unsurprising: for
any fixed problem size, a polynomial-time adversary can still achieve
arbitrarily good probability, because the property of being polynomial-time is
vacuous if the problem size is fixed.

This is not as severe an issue as it may seem: we can assume (without
formalising it in Agda) that $\epsilon$ is small, and interpret the
indistinguishability results we come to in this light.  This is how many proofs
in the literature are written as is.\todo{cite something}  On the other hand, a
more elegant approach is to look at asymptotic indistinguishability.

Instead of assuming that games |G adv| and |H adv| are
$\epsilon$-indistinguishable, we can assume that the families of games |G n adv|
and |H n adv| are $f(n)$-indistinguishable, where $f$ is a function with limit
$0$ as $n$ goes to infinity.  The value $n$ is typically called the
\emph{security parameter}.  This approach allows us to show within Agda that |G|
and |H| are harder to distinguish at higher security levels.

\section{Future Work}

In this chapter, we have specified the foundations of a theory of
indistinguishability of games.  An important further step is to develop a
collection of lemmas based on this theory that can act as rewrite rules for
games.  Bellare and Rogaway~\cite{codebasedgames} have identified a number of
techniques that are commonly used in cryptographical proofs, and a formalisation
of these would greatly improve the practical value of this theory.

In particular, the `identical until bad' technique~\cite{gameexamples} tells us
that if two games |X| and |Y| are identical unless some bad event |F| happens
and |F| has probability $\epsilon$, then |X| and |Y| are in fact
$\epsilon$-indistiindistinguishable.  For example, two games may be
indistinguishable unless two uses of |uniform n| result in the same bitstring,
or if the adversary can find a string that causes a hash collision.  This 
technique is very useful, but it is hard to formalise in our context: we may not
be able to tell from the final state of the game whether the bad event happened.
As such, we need to show that the game is result-indistinguishable from one
that adds additional instrumentation to track the bad event, and then use the
data provided by this instrumentation to reason that the games can only differ
in a minority of cases.  This is hard to do even in concrete scenarios, and a
general solution would be useful for formalising existing proofs.

\todo{inline}{Bernoulli?}

We have also been unable to develop the equational theory with oracles to the
same point as the theory without them.  There does not appear any fundamental
reason we could not find comparable results for canonical forms.  However, these
developments may be better done in the context of \autoref{sec:cs-multiplayer},
where we perform a further generalisation of oracles.

The distinction between indistinguishability and result-indistinguishability
is a considerable source of complexity throughout this chapter.  We have not
thoroughly studied the connection between the two: we conjecture that we can
recover indistinguishability from result-indistinguishability by defining a
|preserve| map that sends a game |X| to |getState >>= \ st -> X >>= \ a ->
setState st >> return a| and arguing that if games |X| and |Y| are
result-indistinguishable, then |preserve X| and |preserve Y| are
indistinguishable.  However, even this is not very satisfactory, and we explore
a better approach in \autoref{sec:im-player-state-types}.

Finally, not all conseuences of the point-free presentation of
indistinguishability we have given here are clear to us.  In particular, we
may wish to work with the support of a distribution, and we do not yet know how
this can be expressed in this system.