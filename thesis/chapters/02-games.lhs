\chapter{Representing Games}

\todo{Why?}
The games we considered in \autoref{chp:introduction} are sequences of
instructions, where later instructions can depend on the results of earlier
ones.  In order to be able to formulate properties of these games within Agda,
we would like to retain as much of their syntactic structure as possible.  We
therefore use a free monad construction to obtain the most general type that
supports the operations we require and has a monadic bind.

We start by introducing a datatype for games and showing that it has the
properties we are interested in.  This datatype supports the essential
operations we expect from games: generating a uniformly random bitvector, and
reading and writing the state.  We then show how this language can be extended
to support oracle use and how we can impose constraints on such use.

\todo{Where do these ideas come from?}

\section{Free Monads}

As we have seen in the introduction, a game with result |A| either immediately
returns a pure |a : A|, or issues a command |c| and then handles the response,
returning a new game.  Assuming that our operations are to generate a uniformly
random bitvector of a given length, get the state (of some fixed type |ST|), or
set the state, this gives rise to the following datatype.
\begin{code}
data CryptoExpr (ST : Set) : Set -> Set where
  Return    : A                                               -> CryptoExpr ST A
  Uniform   : (n : Nat)  ->  (BitVec n  ->  CryptoExpr ST A)  -> CryptoExpr ST A
  GetState  :                (ST        ->  CryptoExpr ST A)  -> CryptoExpr ST A
  SetState  : ST         ->  (top       ->  CryptoExpr ST A)  -> CryptoExpr ST A
\end{code}

In the |SetState| case, we could choose to use |CryptoExpr ST A| as the type of
the handler, since it is equivalent to |top -> CryptoExpr ST A|.  We choose not
to do this for the sake of uniformity.

This definition gives rise to a monad |CryptoExpr ST|.  The definitions of
|fmap| and |>>=| are as follows.  We only give the |Return| and |Uniform| cases,
since the others are analogous.  |Return| plays the role of |return|.
\begin{code}
fmapCE : (A -> B) -> CryptoExpr ST A -> CryptoExpr ST B
fmapCE f (Return a)        = Return (f a)
fmapCE f (Uniform n cont)  = Uniform n \ v -> fmapCE f (cont v)

bindCE : CryptoExpr ST A -> (A -> CryptoExpr ST B) -> CryptoExpr ST B
bindCE f (Return a)        = f a
bindCE f (Uniform n cont)  = Uniform n \ v -> bindCE (cont v) f
\end{code}

The monad laws can be shown to hold if we assume functional
extensionality.\todo{Dependent?}

We would like to keep the constructors of |CryptoExpr| hidden and write our
games in terms of monadic actions that we combine with |>>=|.  We can do this by
passing |Return| as the continuation.  This lets us treat basic operations like
|uniform| and derived operations the same way.
\begin{code}
uniform : (n : Nat) -> CryptoExpr ST (BitVec n)
uniform n = Uniform n Return

coin : CryptoExpr ST Bool
coin = fmap head (uniform 1)

modify : (ST -> ST) -> CryptoExpr ST ST
modify f = do
  st <- getState
  let st' = f st
  setState st'
  return st'
\end{code}

A considerable problem with this approach is that despite the definitions of
|fmapCE| and |bindCE| having almost identical cases for each command, there is
no easy way to avoid the duplication.  We will later see how the constructions
performed so far can be generated automatically given a specification of
commands and responses.

\section{IND-EAV}

This consturction allows us to write simple games such as the IND-EAV game from
\autoref{chp:introduction}.  We start by specifying what an encryption scheme
and an adversary are.  Suppose that we have fixed the types |K|, |PT| and |CT| of
keys, plaintext messages, and ciphertext messages respectively.

\begin{code}
record EncScheme : Set1 where
  field
    keygen : forall {ST} -> CryptoExpr ST A
    enc : forall {ST} -> K -> PT -> CryptoExpr ST CT

record EAVAdversary (ST : Set) : Set where
  field
    A1 : CryptoExpr ST (PT * PT)
    A2 : CT -> CryptoExpr ST Bool
\end{code}

Note that the encryption scheme is parametric in the state type.  We assume, for
now, that any information needed in |enc| and |dec| is passed explicitly via the
key.  This is a considerable simplification, as it means the only player with
state is the adversary, and no questions of how state should be shared arise.

We can now define the EAV-IND game much as we did in \autoref{chp:introduction}.
We fix an |enc : EncScheme|.  Since Agda 2.5.4 supports |do| notation we make
use of it, though the equivalent program could of course be written using |>>=|
explicitly.

\begin{code}
open EncScheme enc
INDEAV : forall{ST} -> EAVAdversary ST -> CryptoExpr ST Bool
INDEAV adv = do
  k <- keygen
  m1 , m2 <- A1 adv
  b <- coin
  ct <- enc (if b then m1 else m2)
  b' <- A2 adv ct
  return $ isYes (eq b b')
\end{code}

\todo{Some kind of conclusion here?}

\section{Representing Oracles}

For the purposes of this chapter, we will consider oracles that support two
operations: they can be initialised using some value of type |OracleInit|, and
they can be queried by passing an |OracleArg|, to which they will respond with
by returning an |OracleResult|.  We will look at how oracles with more
operations can be supported in \autoref{chp:command-structures}.

We can specify oracles in the same way we specified adversaries, by defining a
record that maps their operations to games.
\begin{code}
record Oracle (OST : Set) : Set where
  field
    Init : OracleInit -> CryptoExpr OST top
    Call : OracleArg -> CryptoExpr OST OracleResult
\end{code}

However, we cannot pass these implemantations to the adversary as we passed the
adversary implementations to the challenger, since they would then share state
types.  We must specify the oracle and adversary in such a way that neither has
any syntactic possibility to inspect the other's state.

We can do this by extending the language of adversaries with commands for oracle
initialisation and oracle call operations.  We get a new type
|OracleExpr|\todo{Better name} that has the same constructors as |CryptoExpr|
together with two new ones.  Note that |OracleExpr| is thus ``a game with access
to an oracle'', not ``a game that implements an oracle.''
\begin{code}
data OracleExpr (ST : Set) : Set -> Set where
  Return      : A                                                    -> OracleExpr ST A
  Uniform     : (n : Nat)   ->  (BitVec n      ->  OracleExpr ST A)  -> OracleExpr ST A
  GetState    :                 (ST            ->  OracleExpr ST A)  -> OracleExpr ST A
  SetState    : ST          ->  (top           ->  OracleExpr ST A)  -> OracleExpr ST A
  InitOracle  : OracleInit  ->  (top           ->  OracleExpr ST A)  -> OracleExpr ST A
  CallOracle  : OracleArg   ->  (OracleResult  ->  OracleExpr ST A)  -> OracleExpr ST A
\end{code}

This construction gives rise to a monad the same way as |CryptoExpr ST| does.
Note that we overload the |CryptoExpr| constructors; since their meaning is the
same, we trust this does not cause confusion.

Now we can specify an adversary with state type |AST| as a |OracleExpr AST A|
and an oracle with state type |OST| as an |Oracle OST|, and then combine them
together to obtain a |CryptoExpr (AST * OST) A| which can be regarded as a game.
We know that in any game constructed this way, the adversary cannot inspect or
modify the oracle state, since there is simply no way to write such an
operation.

We can now define this gluing.  An essential property we use is that a
|CryptoExpr ST| can be transformed into a |CryptoExpr (X * ST)| for every |X|,
since this allows us to embed the computations performed by the oracle into the
rest of the game.
\begin{code}
embedState : CryptoExpr T A -> CryptoExpr (S * T) A
embedState (Return a) = Return a
embedState (Uniform n cont) = Uniform n \ v -> embedState (cont v)
embedState (GetState cont) = GetState \ st -> embedState (cont (snd st))
embedState (SetState st cont)
  = modify (second $ const st) >>= \ _ -> embedState (cont tt)
\end{code}

We now fix an oracle implementation with state type |OST| and define the gluing
as follows.
\begin{code}
eval : OracleExpr AST A -> CryptoExpr (AST * OST) A
eval (Return a) = Return a
eval (Uniform n cont)       = Uniform n \ v -> eval (cont v)
eval (GetState cont)        = GetState \ st -> eval (cont (fst st))
eval (SetState st cont)     = modify (first $ const st) >>= \ st -> eval (cont tt)
eval (InitOracle st cont)   = embedState (Impl st) >>= \ _ -> eval (cont tt)
eval (CallOracle arg cont)  = embedState (Call arg) >>= \ r -> eval (cont r)
\end{code}

This gives us a syntax for representing both oracles and adversaries and a way
of putting such a syntactic description back into a single description of a
game.

This presentation is good on paper, and so we will continue to use it throughout
this thesis.  If we need to, we can extend the oracle with more operations by
adding corresponding fields to |OracleImpl| and constructors to |OracleExpr|.
Unfortunately, while this addition is simple conceptually, performing it in
practice leads to considerable code duplication.  We will see how this can be
avoided in \autoref{chp:command-structures}.


\section{Constraints on Adversaries}

We can now express all the games we want to, and we tackle the opposite problem:
how can we restrict the space of games, for example to restrict the class of
adversaries that we are considering?

Let us start by considering a simpler example: suppose we want to require that
a |CryptoExpr ST A| does not read or write from the state; in other words,
restrict the operations to only |Return| and |Uniform|.  We can express a
predicate on games that is only true for those that only use those two commands:
\begin{code}
data Stateless : CryptoExpr ST A -> Set1 where
  ReturnS   : forall a -> Stateless (Return a)
  UniformS  : forall n
            -> {cont : BitVec n -> CryptoExpr ST A}
            -> (forall v -> Stateless (cont v))
            -> Stateless (Uniform n cont)
\end{code}

This is where the syntactic representation of games pays off: since we have not
yet interpreted the operations, we can mimic the structure of |CryptoExpr|,
including only the cases we wish to allow.  Note that we can extend our
|CryptoExpr| datatype with new constructors, but we will not be able to
construct |Stateless| proofs for them unless we add the corresponding
constructors to |Stateless| as well.

We can also use this technique to bound the number of times an adversary queries
the oracle, and restrict the adversary from reinitialising the oracle.  In this
case, we have a relation between games |ce|, natural numbers |k|, and booleans
|b|, representing that game |ce| queries the oracle at most |k| times and does
not initialise the oracle if |b| is false.  We can encode this in Agda as
follows:

\begin{code}
data BoundedOracleUse (ST : Set) : Bool -> Nat -> OracleExpr A -> Set1 where
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
one.  Note that this is only a restriction on what the game is \emph{allowed} to
do: since the |ReturnBOU| case does not restrict |b| or |k|, we do not require
the game to perform any actions.  If we wanted to, we could achieve the latter
effect by changing the |ReturnBOU| constructor to always give |BoundedOracleUse
false 0 (Return a)|.

If all the response types involved are finite, we can enumerate all the possible
command-response sequences and thereby decide whether a game satisfies a
property formulated this way.  In the case of |Stateless|, this is possible
since the only responses that we are interested in are of type |BitVec n|, which
is certainly finite.  Suppose then that we have an enumeration |allbitvecs n| of
|BitVec n|.  Then we can define such a decider as follows.
\begin{code}
isStateless : CryptoExpr ST A -> Bool
isStateless (Return a) = true
isStateless (Uniform n cont)
  = all (map (\ v -> isStateless (cont v)) (allbitvecs n)
isStateless (GetState _) = false 
isStateless (SetState _ _) = false 
\end{code}

We can express soundness of |isStateless| in Agda by defining a function
\begin{code}
isStatelessSound : IsTrue (isStateless ce) -> Stateless ce
\end{code}
which gives a proof of |Stateless ce| for any |ce| such that |isStateless ce|
evaluates to true.  The proof of this relies on some details of working with
lists that we would rather not get into here.\todo{Appendix?}

At first glance, this seems like a useful feature as we can now use
|isStatelessSound true| instead of constructing a proof explicitly, at least
when the term |ce| is closed.  However, this proof search algorithm has to
iterate over every possible |BitVec n|, since it has no way to inspect the
continuation directly.  As such, even on simple cases such as |isStateless
(uniform n)|, the algorithm will take $O(2^n)$ time to run, making it unusable
in practice.

However, these predicates are still very useful when we want to restrict the
behaviour of an adversary, since in that case we can take such a proof as a
parameter.  We will see another way of imposing such constraints in
\autoref{chp:indexed-monads}.\todo{Conclusion?}
