\chapter{The Logic of Games}
\label{chp:proofs}

Throughout \autoref{chp:introduction}, we argued that rewrite steps were valid
because they produced $\epsilon$-indistinguishable games.  In this chapter,
we will define this notion of $\epsilon$-indistinguishable formally, thereby
specifying the logic that can be used to reason about games.  Keeping with the
style of the previous chapter, we will do this in a purely syntactic way; we
will consider the semantics of this relation in \autoref{chp:interpretation}.

Before we dive in to the technical details, let us consider what relation we
would like to capture.  Two games with result type |A| being
$\epsilon$-indistinguishable means that up to some error term $\epsilon$, the
probability of sampling any |a : A| from one is close to the probability of
sampling |a| from the other.  An interesting point in our construction is that
we will formalise this notion with no reference to the individual elemenst of
|A|.

We will start this chapter by looking at how we can define
$\epsilon$-indistinguishability in classical probability theory, and what
results hold there.  We will then define the $\epsilon$-indistinguishability
relation |==eE| on terms of type |CryptoExpr ST A| and prove some results about
it.  In particular, we will show that the full power of monads is not necessary
to represent arbitrary games: up to indistinguishability, every game has a fixed
structure.

We will proceed to consider two basic variations of the
$\epsilon$-indistinguishability relation.  First of all, we will note that the
relation we defined is too strong: there are games we considered
$\epsilon$-indistinguishable in \autoref{chp:introduction}, but which are not
$\epsilon$-indisindistinguishable in this new system.  This is because in our
earlier examples, we ignored the final adversary state when we reasoned about
the games.  To correct this, we will introduce a new relation called result
$\epsilon$-indistinguishability that will make our proofs go through again.  For
the second variation, we will show how $\epsilon$-indistinguishability can be
extended to games that make use of an oracle.

Finally, we will consider how this system handles the requirements we posed in
\autoref{sec:intro-weaker}, such as asymptotic complexity and the usage of
security assumptions in proofs.  We also discuss a number of problems we have
been unable to solve.

Throughout this chapter, we will make use of the type |Q| of rational numbers to
represent probabilities.  Our construction is independent of the implementation
of the rationals used, as long as arithmetic and ordering is supported.

\section{Properties of Distributions}
\label{sec:proofs-dists}

Before we start on a formalisation in Agda, let us recall how probability
distributions behave in classical mathematics.  All of the material in this
section is long-known and completely standard, but we feel that this brief recap
will serve as motivation for our definition of |==eE|   In particular, we are
interested in exploring how |==eE| should interact with monadic binding.

Since all of the distributions we will consider arise from a bounded number of
coin flips, we are interested exclusively in discrete probability distributions
with finite support.  We will model a probability distribution $X$ over a set
$A$ as a function $f_X : A \to \mathbf{R}$, where for every $a \in A$, $f_X(a)$
gives the probability of drawing $a$ from $X$.  As usual, these functions
satisfy $f_X(a) \in [0, 1]$ and $\sum_{a \in A} f_X(a) = 1$.  If there is no
risk of confusion, we will write $X(a)$ for $f_X(a)$.

To give a better understanding of this presentation, let us consider two
examples that we will need later:
\begin{itemize}
    \item For any set $A$ and any $a \in A$, the Dirac delta distribution $1_a$
    is the distribution that always gives $A$, given by $1_a(a) = 1$ and $1_a(x)
    = 0$ if $x \neq a$.
    \item Let $2^n$ be the set of bit vectors of length $n$.  The uniform
    distribution $U_n$ is defined by $U_n(v) = 2^{-n}$ for every $v \in 2^n$.
\end{itemize}

Given a distribution $X$ over $A$ and an $A$-indexed family of distributions $Y$
over $B$, we define the composite distribution $XY$ over $B$ by
\[
    XY(b) = \sum_{a \in A} X(a)Y_a(b).
\]

It is an easy exercise to show that this this defines a probability
distribution, and that if $X$ and each $Y_a$ have finite support, then $XY$ also
has finite support.

Given two distributions $X$ and $Y$ over the same set $A$, we denote the
distance between them as $\norm{X - Y}$ and define it as
\[ \norm{X-Y} = \frac{1}{2} \sum_{a \in A} \abs{X(a) - Y(a)}. \]

The reader may notice that this is simply the $l^1$ or Manhattan norm from
linear algebra scaled by $\frac{1}{2}$.  The following theorem motivates this
scaling:

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

There is a connection between this notion of composition of probability
distributions and the way in which our games form a monad.  Namely, let $D_A$
denote the set of probability distributions over a set $A$.  We can regard
$D_{-}$ as a functor on $\mathbf{Set}$ and define the action on a function $f :
A \to B$ by \[ D_f(X)(b) = \sum_{a \in f^{-1}(b)} X(a). \]  More importantly for
us, $D_{-}$ has the structure of a monad, with $1_{-}$ being the unit and
composition of distributions being the bind!

We encourage the motivated reader to derive the monad multiplication and check
the monad laws.  Our focus, however, lies on the interaction between the monadic
structure and the norm we defined.

Let us say that two probability distributions $X$ and $Y$ are
\emph{$\epsilon$-indistinguishable} iff $\norm{X - Y} \le \epsilon$.  We will
now demonstrate a number of properties that show how composition of probability
distributions interacts with $\epsilon$-indistinguishibility of distributions.
While this does not directly prove anything about games, it suggests what
properties we can reasonably expect to hold for them, and can thus guide what
assumptions we make.

For the rest of this section, let $A$ and $B$ denote arbitrary sets.

\begin{theorem}
    Let $X, Y$ be distributions over $A$ and let $Z$ be an $A$-indexed
    family of distributions over $B$.  Then
    \[ \norm{XZ - YZ} \le \norm{X - Y}. \]
\end{theorem}

\begin{proof}
    Writing out the definition, for any $b \in B$, \[ \abs{XZ(b) - YZ(b)} =
    \abs{\sum_{a \in A} (X(a) - Y(a))Z_a(b)}.\]  By the triangle inequality,
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
    \[ \frac{1}{2}\sum_{b \in B} \abs{XY(b) - XZ(b)} \le
        \frac{1}{2}\sum_{a \in A} X(a)\left(\sum_{b \in B}\abs{Y_a(b) - Z_a(b)}\right)
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

\todo[inline]{Explain why this is worth talking about.}

\section{$\epsilon$-Indistinguishability}
\label{sec:proofs-epsilon-ind}

With this classical intuition in hand, we can now define the relation of
$\epsilon$-indistinguishability on games.  Just like we defined games to be
purely syntactic constructs, we define this relation in a syntactic manner, by
specifying an inductive data type that represents the proofs of
$\epsilon$-indistinguishability.

The definition, in full detail, is available in the Agda code.  However, the
formulation given there is too verbose to be insightful.  We present the same
inductive rules here in a more understandable manner.  After the definition, we
will show the definition of one such rule in its entirety; this should make
clear both the precise meaning of the other rules, and our reluctance to write
them out in full.

As a final preparation, let us introduce two abbreviations that will be useful
in the (recursive) definition of |==eE| itself.  Let |A| and |B| be arbitrary
types.  Firstly, given two games |G| and |H|\footnote{That is, terms of type
|CryptoExpr ST A|.}, we will say ``|G| and |H| are
$\epsilon$-indistinguishable'' to mean |G ==eE H|.  Secondly, given two
|B|-indexed families of games |f| and |g|\footnote{That is, terms of type |B ->
CryptoExpr ST A|.} and a function |h : A -> Q|, we say ``|f| and |g| are
|h|-indistinguishable'' to mean that for every |a : A|, |f a| and |g a| are (|h
a|)-indistinguishable.

Without further ado: for every non-negative |epsilon : Q| and every two types
|A| and |ST|, let |==eE| be the least binary relation on |CryptoExpr ST A| such
that the following properties hold:
\begin{enumerate}
    \item |==eE| is reflexive and symmetric.
    \item If |G ==e1E H| and |H ==e2E I| then |G ==eeE I|.
    \item Every two games are $1$-indistinguishable.
    \item For every |n : Nat|, if |f| and |g| are (|BitVec n|)-indexed families
    of games and |f v ==eE g v| for every |v : BitVec n|, then |Uniform n f ==eE
    Uniform n g|.
    \item If |f| and |g| are |ST|-indexed families of games and |f st ==eE g st|
    for every |st : ST|, then |GetState f ==eE GetState g|.
    \item If |f| and |g| are |top|-indexed families of games and |f tt ==eE g
    tt| then for every |st : ST|, |SetState st f ==eE SetState st g|.
    \item |==eE| is closed under the state monad laws;
    \item \label{li:xchg-uni-gs} |==eE| is closed under the reordering of
    |uniform| and |getState| operations;
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
\end{enumerate}

Let us write out rule \ref{li:xchg-uni-gs} in its entirety.  In Agda, the
statement is as follows:
%format xchgUGS = "\IC{xchg-Uniform-GetState}"
\begin{code}
data _==eE_ (ST A : Set) : (ce cf : CryptoExpr ST A) -> Set where
  ldots
  xchgUGS  : (FORALL n)
           -> (cont : BitVec n -> ST -> CryptoExpr ST A)
           -> (Uniform n \ v -> GetState \ st -> cont v st)
              ==eE (GetState \ st -> Uniform n \ v -> cont v st)
  ldots
\end{code}

Translated to English, this reads: for every |n : Nat| and every continuation
|cont| that sends a bit vector and a state to a game, the following two actions
are equivalent:
\begin{itemize}
    \item generate a random bit vector |v|, retrieve the state |st|, and call
    |cont v st|; and
    \item retrieve the state |st|, generate a random bit vector |v|, and call
    |cont v st|.
\end{itemize}

The other rules are similarly simple in meaning and obscure in formal statement.

Let us now go through a number of results that highlight the similarity of
|==eE| to the notion of $\epsilon$-indistinguishability we defined on
probability distributions in \autoref{sec:proofs-dists}.

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

A special case of |==eE| arises for $\epsilon = 0$.  We denote this relation
|==E| and say that two games |G| and |H| satisfying |G ==E H| are
indistinguishable, dropping the $\epsilon$.  The |==E| relation is of great
practical value since it allows us to replace multiple occurences of a subgame
at once.  This will be particularly important when we look at games that make
use of an oracle.

Now that we have investigated the basic properties of this logic, let us look at
our first useful result: that every game can be rewritten into a canonical form.

\begin{definition}
    We say that a game |G : CryptoExpr ST A| is in canonical form if there exist
    functions |f : ST -> Nat|, |g : (st : ST) -> BitVec (f st) -> ST|, and |h :
    (st : ST) -> BitVec (f st) -> A| such that |G| is provably equal to
    \begin{code}
    do
        st <- getState
        v <- uniform dollar f st
        setState dollar g st v
        return dollar h st v
    \end{code}
\end{definition}

\begin{theorem}
    Every |G : CryptoExpr ST A| is indistinguishable from a game in canonical
    form.
\end{theorem}

Note that we do not need to assume that the state type |ST| is finite or has
decidable equality.

\begin{proof}
    The full proof is in the Agda code, and proceeds in two steps: we first
    construct |f|, |g|, and |h| and then show indistinguishability.  In all
    cases, the construction is by recursion on the structure of |ce|.

    The key idea of the proof is to explicitly pass around the current state
    |st| and, in the case of |g| and |h|, a sufficiently long vector of
    random bits.  Since |f| does not have access to such a bit vector (being the
    function that determines how much randomness we require), it must enumerate
    all vectors of the right length when the recursion is on a |Uniform|
    constructor.  This makes it unfeasible to explicitly compute this canonical
    form, but we can nevertheless reason with it.

    The main difficulty in the proof is showing that the vector |v : BitVec k|
    provides a sufficient number of random bits.  This involves showing that
    whenever we recurse on a call of the form |Uniform n cont|, we can prove |n
    <= k|.  Careful manipulation of the indices can show this is indeed the
    case.
\end{proof}

\section{Result-Indistinguishability}
\label{sec:proofs-result-ind}

It is tempting to assume that the notion of $\epsilon$-indistinguishability we
have just defined represents $\epsilon$-indistinguishability as we used the term
in \autoref{chp:introduction}.  Unfortunately, the situation is somewhat more
nuanced.

In \autoref{chp:introduction}, we considered games to be indistinguishable even
if they had different effects on the state of the adversary.   We did not have
this luxury when defining the notion of $\epsilon$-indistinguishability above,
since we wanted |==eE| to be a congruence, and thus closed under bind.

When it comes to bounding the advantage of the adversary, however, we do
\emph{not} want to distinguish outcomes based on the state of the adversary: two
adversaries that both win the game with probability 0.5 are equivalent for our
purposes, even if we can distinguish between them based on the effect they have
on the state.  As such, we want a weaker notion of indistinguishability which we
will call result-indistinguishability.

Unfortunately, we have not been able to work out this relation adequately to
present it here.  We nevertheless feel the need to remark on it, as any system
based on this work would require such a relation   We show how an alternative
approach using indexed monads can be used to avoid the need for this relation in
\autoref{chp:indexed-monads}.

\section{Indistinguishability with Oracles}

In order to reason about games involving oracles, we want to extend the notion
of $\epsilon$-indistinguishability to pairs of games involving oracles and
oracle definitions for these games.  We use the fact that we have the |eval|
funcion, which can combine a game involving an oracle and an oracle definition
into a game that makes no mention of oracles.  This gives us a direct way of
defining $\epsilon$-indistinguishability on oracle game-implementation pairs.

%format ocl1 = "ocl\textsubscript{1}"
%format ocl2 = "ocl\textsubscript{2}"
%format ==OE = "\F{$\equiv^{O\!E}$}"
%format ==eOE = "\F{$\equiv_\epsilon^{O\!E}$}"
%format ==eOEocl = "\F{$\equiv_{\epsilon, ocl}^{O\!E}$}"
%format ==eOR = "\F{$\equiv_\epsilon^{O\!R}$}"
Formally speaking, given |G| and |H| of type |OracleExpr AST A| and |ocl1| and
|ocl2| of type |Oracle OST|, we say that |(G , ocl1) ==eOE (H , ocl2)| iff |eval
ce ocl1 ==eE eval cf ocl2|.  We will write |G ==eOEocl H| if |ocl| is the
same on both sides.  We will also write |ocl1 ==eE ocl2|  iff for every |ost :
OracleState|, |Init ocl1 ost ==eE Init ocl2 ost|  and for every |arg : OracleArg|,
|Call ocl1 arg ==eE Call ocl2 arg|.

This is a somewhat unsatisfactory solution, since this does not give us any
reasoning principles for |==eOE|, making the process of proof extremely manual.
We will consider this shortcoming in greater generality in
\autoref{sec:cs-future-work}.


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
two games are $\epsilon$-indistinguishable for
any adversary |adv|:
\begin{code}
do
    st <- getState
    a <- G
    b <- G
    c <- G
    adv (pow g a , pow g b , pow g c)
    setState st

do
    st <- getState
    a <- G
    b <- G
    adv (pow g a , pow g b , pow g (times a b))
    setState st
\end{code}

Notice that we need to explicitly preserve the state due to our lack of a proper
notion of result-indistinguishability.

Nevertheless, we can then use this assumption to replace the usage of |pow g
(times a b)| in a proof with |pow g c|.  For example, this is a key step in
proving the security of the ElGamal encryption scheme~\cite{gameexamples}.  By
introducing this assumption we show that no adversary can find |a| given |pow g
a|, since otherwise they could take |pow (pow g b) a| and compare it to the
third component of the tuple.

A possible downside to this approach is that our assumptions must all be phrased
as statements of indistinguishability. Another issue with this approach is that
while this allows us to reason about an arbitrary adversary as if it satisfied
our assumptions, it does not restrict the class of adversaries that we may use
as a counterexample: it is thus necessary to check the validity of any
constructed adversaries by hand.

Finally, an assumption of this kind only states that such an $\epsilon$ exists,
without any bounds on the size of this $\epsilon$.  This is unsurprising: for
any fixed problem size, a polynomial-time adversary can still achieve
arbitrarily good probability, because the property of being polynomial-time is
vacuous if the problem size is fixed.

This is not as severe an issue as it may seem: we can assume (without
formalising it in Agda) that $\epsilon$ is small, and interpret the
indistinguishability results we come to in this light.  This is not uncommon in
existing proofs~\cite{gameexamples}.  However, if we want a more formal
resolution to this problem, we can reason about asymptotic indistinguishability.

Instead of attempting to prove that games |G| and |H| are
$\epsilon$-indistinguishable, we can instead look at families of games |G| and
|H| parametrised by a security paraeter, and show that they are
$f$-indistinguishable for some vanishing function $f$.  

\todo[inline]{This section still needs some cleanup.}

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

We have also been unable to develop the equational theory with oracles to the
same point as the theory without them.  There does not appear any fundamental
reason we could not find comparable results for canonical forms.  However, these
developments may be better done in the context of \autoref{sec:cs-multiplayer},
where we perform a further generalisation of oracles.  The possible interactions
between oracles and result-indistinguishability are also an interesting matter
of further study.

Finally, not all conseuences of the point-free presentation of
indistinguishability we have given here are clear to us.  In particular, we
may wish to work with the support of a distribution, and we do not yet know how
this can be expressed in this system.
