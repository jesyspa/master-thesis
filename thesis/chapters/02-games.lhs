\chapter{Representing Games}
\label{chp:games}
%{

In \autoref{chp:introduction}, we modelled games as imperative programs,
represented by terms in a suitable monad.  We had assumed the existence of a
monad that supported the operations we require.  In this chapter, we will see
how the free monad construction~\cite{dtalacarte, tctotallyfree} can be used to
define this monad explicitly.  A monad constructed this way supports all the
required operations, but treats them syntactically, without giving them any
further interpretation.

Given that there exist monads both for stateful and
probabilistic~\cite{probfunproghaskell} computations, a natural question is why
we do not define our games in terms of those.  This would be possible, but makes
the subsequent development considerably harder.  The syntactic approach we take
allows us to inspect our games with greater detail.  For example, there is no
way to check whether a term in the state monad makes use of the state, while
being able to do so is convenient for our purposes.  Furthermore, as the term
`free monad' suggests, we can map our games into any monad that supports the
required operations, and so we lose nothing by delaying this interpretation
until it is unavoidable.

We will start by constructing a monad for games that do not make use of an
oracle.  In this case, the only operations we require are |uniform|, |getState|
and |setState| from \autoref{chp:introduction}.  We will then show how the same
techniques can be used to extend this language to support games that do make use
of an oracle.  Finally, we will show how the syntactic nature of this
representation can be used to impose constraints on an adversary.

\section{Free Monads}

From a syntactic point of view, a game with result type |A| can do one of two
things: immediately yield a value of type |A|, or execute some command and then
map the response to another game with result type |A|.  Treating this as an
inductive definition is the key insight of the free monad
construction~\cite{tctotallyfree}.  For our three commands, the free monad can
be defined as follows:
\begin{code}
data CryptoExpr (ST : Set) : Set -> Set where
  Return    : A                                               -> CryptoExpr ST A
  Uniform   : (n : Nat)  ->  (BitVec n  ->  CryptoExpr ST A)  -> CryptoExpr ST A
  GetState  :                (ST        ->  CryptoExpr ST A)  -> CryptoExpr ST A
  SetState  : ST         ->  (top       ->  CryptoExpr ST A)  -> CryptoExpr ST A
\end{code}

When talking about games, we will refer to the constructor and first argument as
the \emph{command}, and the second argument as the \emph{response handler} or
\emph{continuation}.  Note that since |top -> X| is isomorphic to |X| for every
type |X|, we could have used |ST -> CryptoExpr ST A -> CryptoExpr ST A| as the
type of |SetState|.  However, we use the more verbose form for the sake of
consistency with the other constructors.

Although this definition is entirely syntactic, there is an intended semantic
meaning we keep in mind: |Uniform| represents the generation of a uniformly
random bit vector, |GetState| represents a read from the state and |SetState|
represents a write to the state.  We will only define this interpretation in
\autoref{chp:interpretation}, but provides a useful intuition for the
constructions we do in this chapter and the next.

We can define the monadic actions |uniform|, |setState| and |getState| as terms
in the |CryptoExpr ST| monad by passing |Return| as the response handler:
\begin{code}
uniform : (n : Nat) -> CryptoExpr ST (BitVec n)
uniform n = Uniform n Return

getState : CryptoExpr ST ST
getState = GetState Return

setState : ST -> CryptoExpr ST top
setState st = SetState st Return
\end{code}

In order to show that |CryptoExpr ST| is indeed a monad, we take |return =
Return| and define |fmap| and |>>=| as follows:
\begin{code}
fmapCE : (A -> B) -> CryptoExpr ST A -> CryptoExpr ST B
fmapCE f (Return a)          = Return (f a)
fmapCE f (Uniform n cont)    = Uniform n    \ v -> fmapCE f (cont v)
fmapCE f (GetState cont)     = GetState     \ st -> fmapCE f (cont st)
fmapCE f (SetState st cont)  = SetState st  \ t -> fmapCE f (cont t)

bindCE : CryptoExpr ST A -> (A -> CryptoExpr ST B) -> CryptoExpr ST B
bindCE (Return a)          f  = f a
bindCE (Uniform n cont)    f  = Uniform n    \ v -> bindCE (cont v) f
bindCE (GetState cont)     f  = GetState     \ st -> bindCE (cont st) f
bindCE (SetState st cont)  f  = SetState st  \ t -> bindCE (cont t) f
\end{code}

We will see how we can avoid the repetitiveness of these definitions in
\autoref{chp:command-structures}.  For convenience, we also define some
derived operations:
\begin{code}
coin : CryptoExpr ST Bool
coin = fmap head (uniform 1)

modify : (ST -> ST) -> CryptoExpr ST ST
modify f = do
  st <- getState
  let st' = f st
  setState st'
  return st'
\end{code}

Since proving the equality between two games involves proving that their
response handlers are equal, we need functional extensionality to prove that
|CryptoExpr ST| satisfies the monad laws.  Except for this, the proofs are
straightforward.

This concludes the definition of |CryptoExpr ST|, bringing us again to where we
were at the beginning of \autoref{sec:intro-programs}, but this time with
no assumptions.  The motivated reader may wish to go back and check that the
|INDEAV| game presented there can be expressed in this system.

\section{Representing Oracles}
\label{sec:games-oracles}

We will now define another monad for games, which will allow us to express games
where the adversary has access to an oracle.  As in
\autoref{sec:intro-oracles}, we will assume that oracles support two
operations: |initOracle| to initialise the oracle state and |callOracle| to
perform a query to the oracle.  We will consider how this set of operations can
be extended in \autoref{chp:command-structures}.

Recall that |initOracle| takes an |OracleState| value to initialise the oracle
with and gives no response, while |callOracle| takes an |OracleArg| and responds
with an |OracleResult|.  We define |OracleExpr ST|, the type of games that use
an oracle, as follows:
\begin{code}
data OracleExpr (ST : Set) : Set -> Set where
  Return      : A                                                     -> OracleExpr ST A
  Uniform     : (n : Nat)    ->  (BitVec n      ->  OracleExpr ST A)  -> OracleExpr ST A
  GetState    :                  (ST            ->  OracleExpr ST A)  -> OracleExpr ST A
  SetState    : ST           ->  (top           ->  OracleExpr ST A)  -> OracleExpr ST A
  InitOracle  : OracleState  ->  (top           ->  OracleExpr ST A)  -> OracleExpr ST A
  CallOracle  : OracleArg    ->  (OracleResult  ->  OracleExpr ST A)  -> OracleExpr ST A
\end{code}

We could have used different names for the constructors that were already used
in |CryptoExpr|, but since the behaviour in each case is practically identical,
we expect the ambiguity to not cause any issues.

As in the case of |CryptoExpr|, we can define |uniform|, |getState|, and
|setState|, and we can now also define |initOracle| and |callOracle| in the same
way.  Similarly, the definitions of |fmap| and |>>=| are straightforward
extensions of those for |CryptoExpr|.

We can now specify games such as |IND-CPA| from
\autoref{sec:intro-oracles}, but we must also be able to define the
behaviour of the oracles themselves.  We do this much the same way we specify
adversaries, by defining a record that has interpretations for the operations.
Note that we define oracles using the |CryptoExpr| monad, not |OracleExpr|: the
latter would allow an oracle to call itself, potentially leading to a
non-terminating game.  The definition of an oracle implementation is as follows:
\begin{code}
record Oracle (OST : Set) : Set where
  field
    Init : OracleState  -> CryptoExpr OST top
    Call : OracleArg    -> CryptoExpr OST OracleResult
\end{code}

We will use |OST| to refer to the type of the state that the oracle stores, and
use |AST| (instead of |ST|) for the state type of the adversary.

In order to reason about a game that involves oracles, we would like to merge
all the above components into a single game, much the same way we inlined the
definitions of the encryption scheme and adversary when reasoning about |INDEAV|
in \autoref{sec:intro-otp-eav}.  However, the process of combining a game
expressed as an |OracleExpr AST| term and an |Oracle| implementation is somewhat
more complicated than the usage of an adversary in a game, since we need to
reconcile the types |OracleExpr AST| and |CryptoExpr OST|.  In
\autoref{sec:intro-oracles}, we remarked this can be done by using
|CryptoExpr (AST * OST)| to store both states at once.  Let us now formalise
this approach.

We start by defining the operations |getOracleState|, |setOracleState|,
|getAdvState|, and |setAdvState|, which we use for operating on the oracle and
adversary components of the state respectively.  The definitions are as follows:
\begin{code}
getOracleState : CryptoExpr (AST * OST) OST
getOracleState = fmap snd getState

getAdvState : CryptoExpr (AST * OST) AST
getAdvState = fmap fst getState

setOracleState : OST -> CryptoExpr (AST * OST) top
setOracleState ost = do
  ast <- getAdvState
  setState dollar ast , ost

setAdvState : AST -> CryptoExpr (AST * OST) top
setAdvState ast = do
  ost <- getOracleState
  setState dollar ast , ost
\end{code}

One last function we need before we can define the gluing is a way of embedding
the terms that implement the oracle, which have type |CryptoExpr OST A|, into
the game as a whole, which has type |CryptoExpr (AST * OST) A|.  Fortunately,
this is straightforward given the functions we defined above, since we can
replace all uses of |GetState| by |getOracleState| and |setState| by
|setOracleState|:
%format embed = "\F{embed}"
\begin{code}
embed : CryptoExpr OST A -> CryptoExpr (AST * OST) A
embed (Return a)          = Return a
embed (Uniform n cont)    = Uniform n \ v -> embed (cont v)
embed (GetState cont)     = getOracleState     >>= \ st  -> embed (cont st)
embed (SetState st cont)  = setOracleState st  >>= \ t   -> embed (cont t)
\end{code}

Now we have all the tools necessary to define a function that combines a game
that uses an oracle and a definition of that oracle into a single game.  The
idea is much the same as in |embed|: we replace uses of |getState| and
|setState| by |getAdvState| and |setAdvState| respectively, and use the |embed|
function to embed the oracle implementation where it is used.
\begin{code}
eval : Oracle OST -> OracleExpr AST A -> CryptoExpr (AST * OST) A
eval ocl (Return a) = Return a
eval ocl (Uniform n cont)       = Uniform n \ v -> eval ocl (cont v)
eval ocl (GetState cont)        = getAdvState     >>= \ st  -> eval ocl (cont st)
eval ocl (SetState st cont)     = setAdvState st  >>= \ t   -> eval ocl (cont t)
eval ocl (InitOracle st cont)   = embed (Init ocl st)   >>= \ t  -> eval ocl (cont t)
eval ocl (CallOracle arg cont)  = embed (Call ocl arg)  >>= \ r  -> eval ocl (cont r)
\end{code}

With this in place, we can represent the examples from
\autoref{sec:intro-oracles} within our system.  Most importantly, this gives us
an automatic way of performing the inlining that we did by hand in
\autoref{sec:intro-otp-cpa}, allowing us to detect when we have made a mistake.

We would like to highlight the role of the free monad construction in enabling
this straightforward approach to oracles.  Had we defined |CryptoExpr| in a less
syntactic way, extending it with further operations would be far more difficult.
As it is, such an extension can be performed by adding more constructors to
|OracleExpr| and adding corresponding constructors to |Oracle|.  We will see how
this system can be improved further in \autoref{chp:command-structures}, so that
the definitions of |fmap| and |>>=| do not need to be updated when such changes
are made.


\section{Constraints on Adversaries}
\label{sec:games-constraints}

We can now express all the games we have outlined in \autoref{chp:introduction}.
Let us tackle the opposite problem: how can we place a restriction on what a
|CryptoExpr| or |OracleExpr| term may do, for example to restrict the class of
adversaries?

We can start by considering a simple example: suppose that we want some portion
of our game to not have access to the state; for example, if we want to express
that an implementation of the oracle may not use the state.  We could achieve
this by removing state from the games entirely, or by setting its type to |top|,
but both of these are big changes that affect the system as a whole.
Instead, we can define a |Stateless| predicate on terms |ce : CryptoExpr ST A|
that holds only if |ce| does not use the |GetState| or |SetState| constructors.
We can define this as follows:
\begin{code}
data Stateless : CryptoExpr ST A -> Set where
  ReturnS   : forall a -> Stateless (Return a)
  UniformS  : forall n
            -> {cont : BitVec n -> CryptoExpr ST A}
            -> (forall v -> Stateless (cont v))
            -> Stateless (Uniform n cont)
\end{code}

If a game is expressed exclusively in terms of |Return| and |Uniform|, then we
can construct a corresponding proof term using |ReturnS| and |UniformS| by
following the recursive structure.  However, if the game uses |GetState| or
|SetState|, then no proof can exist, since |Stateless (GetState cont)| and
|Stateless (SetState st cont)| can be shown to be empty.  We can thus use the
type |Sigma (CryptoExpr ST A) Stateless| to represent the type of games that use
no state within Agda itself.

We can also use this technique to bound the number of times an adversary queries
the oracle, and restrict the adversary from reinitialising the oracle.  We can
make a predicate |BoundedOracleUse k b| on terms |ce : OracleExpr ST A| that
expresses that |ce| uses |CallOracle| at most |k| times, and only uses
|InitOracle| if |b| is |true|.   Just like with |Stateless|, we represent this
in Agda by creating a datatype that mimics the recursive structure of
|OracleExpr|.
\begin{code}
data BoundedOracleUse : Bool -> Nat -> OracleExpr A -> Set1 where
  ReturnBOU      : forall a -> BoundedOracleUse b k (Return a)
  UniformBOU     : {cont : BitVec n -> OracleExpr A}
                 -> (forall v -> BoundedOracleUse b k (cont v))
                 -> BoundedOracleUse b k (Uniform n cont)
  GetStateBOU    : {cont : ST -> OracleExpr A}
                 -> (forall  st -> BoundedOracleUse b k (cont st))
                 -> BoundedOracleUse b k (GetState cont)
  SetStateBOU    : {ce : OracleExpr A}
                 -> BoundedOracleUse b k ce
                 -> BoundedOracleUse b k (SetState st ce)
  InitOracleBOU  : {ce : OracleExpr A}
                 -> BoundedOracleUse false k ce
                 -> BoundedOracleUse true k (InitOracle st ce)
  CallOracleBOU  : {cont : OracleResult -> OracleExpr A}
                 -> (forall  r -> BoundedOracleUse b k (cont r))
                 -> BoundedOracleUse b (suc k) (CallOracle arg cont)
\end{code}

Note that in the |InitOracleBOU| case we require the continuation to have no
|InitOracleBOU| calls, thus forcing initialisation to happen at most once, and
in |CallOracleBOU|, we decrease the number of allowed calls to the oracle by
one.  It is worth mentioning that this is only a restriction on what the game is
\emph{allowed} to do: since the |ReturnBOU| case does not restrict |b| or |k|,
we do not \emph{require} the game to perform any actions.  If we wanted to, we
could achieve the latter effect by changing the |ReturnBOU| constructor to
have type |forall a -> BoundedOracleUse false 0 (Return a)|.

This approach works very well when we want to restrict some property of a |ce :
CryptoExpr ST A| (or |OracleExpr|) we receive as an input, since we can add an
extra parameter that represents a proof that |ce| satisfies some property.
However, a drawback of this approach is that when \emph{we} construct a |ce :
CryptoExpr ST A|, we must also construct the corresponding proof.  This is not
difficult, since the proof term is completely determined by |ce| itself, but it
the kind of work we would like to automate.

The straightforward way to do this in Agda would be to traverse the |CryptoExpr
ST A| structure and check that the conditions we impose are satisfied.  In the
case of |Stateless|, this can be done, since |BitVec n| is finite.  Given an
enumeration |allbitvecs : (n : Nat) -> List (BitVec n)| of all bit vectors of a
given length, we can define a runtime predicate |isStateless| by recursion:
\begin{code}
isStateless : CryptoExpr ST A -> Bool
isStateless (Return a) = true
isStateless (Uniform n cont)
  = all (map (\ v -> isStateless (cont v)) (allbitvecs n)
isStateless (GetState _) = false 
isStateless (SetState _ _) = false 
\end{code}

We can express the soundness of |isStateless| in Agda by defining a function
that takes a proof that |isStateless ce| is |true| and gives a proof of
|Stateless ce|.  Unfortunately, even though this allows us to compute these
proofs automatically, this approach is not useful in practice: enumerating all
bit vectors of length $n$ will take time $\Omega(2^n)$.

Instead, we require some way of generating a proof term based on the syntactic
structure of a term.  In \autoref{chp:indexed-monads} we will show how we can
use indexed monads to incorporate a predicate such as |BoundedOracleUse| in the
definition of |OracleExpr|.  An alternative approach, which we have not had time
to explore, is to use reflection to obtain a description of the structure
of a term as it is in the program code.  This would allow the automatic
generation of proof terms using considerably less time.

Despite these shortcomings, the predicates we defined in this section satisfy
the requirements we posed in \autoref{sec:intro-weaker}, and thus we can now
represent all games we had set out to.  In the next chapter, we will work out
the system for reasoning about these games.

%}
