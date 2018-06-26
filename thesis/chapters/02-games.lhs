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
    dec : forall {ST} -> K -> CT -> CryptoExpr ST PT

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
embedState (ReturnFM a) = ReturnFM a
embedState (InvokeFM (Uniform n) cont)
  = InvokeFM (Uniform n) \ v -> embedState (cont v)
embedState (InvokeFM  GetState cont)
  = InvokeFM GetState \ st -> embedState (cont (snd st))
embedState (InvokeFM (SetState st) cont)
  = modify (second $ const st) >>= \ _ -> embedState (cont tt)
\end{code}

We now fix an oracle implementation with state type |OST| and define the gluing
as follows.
\begin{code}
eval : CryptoOracleExpr AST A -> CryptoExpr (AST * OST) A
eval (ReturnFM a) = ReturnFM a
eval (InvokeFM (false  , Uniform n) cont)       = InvokeFM (Uniform n) \ v -> eval (cont v)
eval (InvokeFM (false  , GetState) cont)        = InvokeFM GetState \ st -> eval (cont (fst st))
eval (InvokeFM (false  , SetState st) cont)     = modify (first $ const st) >>= \ st -> eval (cont tt)
eval (InvokeFM (true   , InitOracle st) cont)   = embedState (Impl st) >>= \ _ -> eval (cont tt)
eval (InvokeFM (true   , CallOracle arg) cont)  = embedState (Call arg) >>= \ r -> eval (cont r)
\end{code}

Oracles can be implemented in the language we have here.  Adversaries can use
the language, but also need it extended with two new operations.  There is no
easy way of doing that; we really need to repeat the construction, but we omit
here as it is clear.  Later we will see how we can generalise.

There is now an evaluation function that takes a game in the language with
oracle calls and an oracle implementation and puts together a game in the
language we started with.

\section{Constraints on Adversaries}

We have seen that for some games, we want to require that adversaries are
restricted in some way, for example to not be allowed to initialise the oracle,
or use it too many times.   We can require a proof that the adversary satisfies
these constraints as follows:

\begin{code}
data BoundedOracleUse : Bool -> Nat -> CryptoExpr A -> Set1 where
  ReturnBOU       : (a : A) -> BoundedOracleUse b k (Return a)
  UniformBOU      : (cont : BitVec n -> CryptoExpr A)
                  -> (forall v -> BoundedOracleUse b k (cont v))
                  -> BoundedOracleUse b k (Uniform n cont)
  GetAdvStateBOU  : (cont : AdvState -> CryptoExpr A)
                  -> (forall  st -> BoundedOracleUse b k (cont st))
                  -> BoundedOracleUse b k (GetAdvState cont)
  SetAdvStateBOU  : (ce : CryptoExpr A)
                  -> BoundedOracleUse b k ce
                  -> BoundedOracleUse b k (SetAdvState st ce)
  InitOracleBOU   : (ce : CryptoExpr A)
                  -> BoundedOracleUse false k ce
                  -> BoundedOracleUse true k (InitOracle st ce)
  CallOracleBOU   : (cont : OracleResult -> CryptoExpr A)
                  -> (forall  r -> BoundedOracleUse b k (cont r))
                  -> BoundedOracleUse b (suc k) (CallOracle arg cont)
\end{code}

Note that in the |InitOracleBOU| case we require the continuation to have no
|InitOracleBOU| calls, thus forcing initialisation to happen exactly once, and
in |CallOracleBOU|, we decrease the number of allowed calls to the oracle by
one.  Note that this is only a restriction on what the game is \emph{allowed} to
do: since the |ReturnBOU| case does not restrict |b| or |k|, we do not require
the game to perform any actions.

Proof search on these things: we could, potentially, do something like:
\begin{code}
hasBOU : Bool -> Nat -> CryptoExpr A -> Bool
hasBOUsound : IsTrue (hasBOU b k ce) -> BoundedOracleUse b k ce
\end{code}

Now, given a concrete term |ce| we can use the evaluation mechanism of Agda
itself to convince it that |IsTrue (hasBOU b k ce)| is |top| and thus that we
can pass |true| to get a proof.

There are a few problems with this.  First of all, this does not work in full
generality: we need to assume that the types |OracleInit|, |OracleResult|, etc. are
all finite, since otherwise we must enumerate an infinite domain.  Secondly, and
more problematically in practice, even given this assumption this code must
check an exponential number of cases when |Uniform| is used.  This makes it
impractical for real cases.  Finally, we typically are not dealing with a
concrete |CryptoExpr|: rather, it is parametrised by the security parameter.
This means we have to prove |IsTrue (hasBOU b k ce)| by hand, which is no easier
than just proving |BoundedOracleUse b k ce|.

Similar consraints can be imposed on e.g. not using randomness, not using state,
etc.  We will see how this can be handled in a different way in
\autoref{chp:indexed-monads}.


