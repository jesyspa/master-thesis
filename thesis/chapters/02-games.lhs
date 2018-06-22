\chapter{Representing Games}

A game is a sequence of instructions.  Although we will later see that tracking
which player executes a given instruction can be useful later, for now we will
develop a system where this information is not preserved.

Instructions can be pure computations, but can also use randomness, state, and
call an oracle.  Note that as above, we do not yet specify what an oracle does:
the game assumes that this will be filled in later.  For a unified treatment,
see chapter \autoref{chp:interaction-structures}.

\section{Free Monads}

We start by introducing a language for stateful probabilistic computations.  We
represent these computations syntactically using a free monad.  We parametrise
our construction over the type of the state.

\begin{code}
data CryptoExpr (ST : Set): Set -> Set where
  Return    : A                                             -> CryptoExpr ST A
  Uniform   : (n : Nat)  -> (BitVec n ->  CryptoExpr ST A)  -> CryptoExpr ST A
  GetState  :            -> (ST       ->  CryptoExpr ST A)  -> CryptoExpr ST A
  SetState  : ST         ->               CryptoExpr ST A   -> CryptoExpr ST A
\end{code}

We can define a monad structure on this.  The instances look as follows (the
other cases are essentially the same):
\begin{code}
fmapCE : (A -> B) -> CryptoExpr ST A -> CryptoExpr ST B
fmapCE f (Return a)        = Return (f a)
fmapCE f (Uniform n cont)  = Uniform n \ v -> fmapCE f (cont v)

bindCE : CryptoExpr ST A -> (A -> CryptoExpr ST B) -> CryptoExpr ST B
bindCE f (Return a)        = f a
bindCE f (Uniform n cont)  = Uniform n \ v -> bindCE (cont v) f
\end{code}

In order to make this easier to use, we can define smart constructors (other
cases again similar):
\begin{code}
uniformCE : (n : Nat) -> CryptoExpr ST (BitVec n)
uniformCE n = Uniform n Return

setStateCE : ST -> CryptoExpr ST top
setStateCE st = SetState st (Return tt)
\end{code}

This allows us to write simple games such as the OTP game from
\autoref{chp:introduction}.  However, note that the state here is shared by all
players.  This is bad, since it means that if we give the adversary access to an
oracle, it will be able to also read the oracle's state.

\section{Using Oracles}

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
itself to convince it that |IsTrue (hasBou b k ce)| is |top| and thus that we
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


