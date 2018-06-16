\chapter{Representing Games}

A game is a sequence of instructions.  Although we will later see that tracking
which player executes a given instruction can be useful later, for now we will
develop a system where this information is not preserved.

Instructions can be pure computations, but can also use randomness, state, and
call an oracle.  Note that as above, we do not yet specify what an oracle does:
the game assumes that this will be filled in later.  For a unified treatment,
see chapter \autoref{chp:interaction-structures}.

\section{Free Monads}

We represent games by free monads.\footnote{Why they are called `free monads'
will be discussed later.}  There are a number of types we must parametrise over:
|AdvState|, |OracleState|, |OracleArg|, |OracleResult|.  Once we've fixed that,
we can define:
\begin{code}
data CryptoExpr : Set -> Set where
  Return       : A                                                 -> CryptoExpr A
  Uniform      : (n : Nat)    -> (BitVec n      ->  CryptoExpr A)  -> CryptoExpr A
  GetAdvState  :              -> (AdvState      ->  CryptoExpr A)  -> CryptoExpr A
  SetAdvState  : AdvState     ->                    CryptoExpr A   -> CryptoExpr A
  InitOracle   : OracleState  ->                    CryptoExpr A   -> CryptoExpr A
  CallOracle   : OracleArg    -> (OracleResult  ->  CryptoExpr A)  -> CryptoExpr A
\end{code}

We can define a monad structure on this.  The instances look as follows (the
other cases are essentially the same):
\begin{code}
fmapCE : (A -> B) -> CryptoExpr A -> CryptoExpr B
fmapCE f (Return a)        = Return (f a)
fmapCE f (Uniform n cont)  = Uniform n (\ v -> fmapCE f (cont v))

bindCE : CryptoExpr A -> (A -> CryptoExpr B) -> CryptoExpr B
bindCE f (Return a)        = f a
bindCE f (Uniform n cont)  = Uniform n (\ v -> bindCE (cont v) f)
\end{code}

In order to make this easier to use, we can define smart constructors (other
cases again similar):
\begin{code}
uniformCE : (n : Nat) -> CryptoExpr (BitVec n)
uniformCE n = Uniform n Return

setAdvStateCE : AdvState -> CryptoExpr top
setAdvStateCE st = SetAdvState st (Return tt)
\end{code}

This allows us to write simple games, but note that it does not allow us to
specify oracles.  We will look at this in the next chapter.

\section{Constraints on Adversaries}

We have seen that for some games, we want to require that adversaries are
restricted in some way, for example to not be allowed to initialise the oracle,
or use it too many times.   We can require a proof that the adversary satisfies
these constraints as follows:

\begin{code}
data BoundOracleUse : Nat -> CryptoExpr A -> Set1 where
  ReturnBOU       : forall k (a : A) -> BoundOracleUse k (Return a)
  UniformBOU      : forall k n
                  -> (cont : BitVec n -> CryptoExpr A)
                  -> (forall v -> BoundOracleUse k (cont v))
                  -> BoundOracleUse k (Uniform n cont)
  GetAdvStateBOU  : forall k (cont : AdvState -> CryptoExpr A)
                  -> (forall  st -> BoundOracleUse k (cont st))
                  -> BoundOracleUse k (GetAdvState cont)
  SetAdvStateBOU  : forall k st (ce : CryptoExpr A)
                  -> BoundOracleUse k ce
                  -> BoundOracleUse k (SetAdvState st ce)
  CallOracleBOU   : forall k arg (cont : OracleResult -> CryptoExpr A)
                  -> (forall  r -> BoundOracleUse k (cont r))
                  -> BoundOracleUse (suc k) (CallOracle arg cont)
\end{code}

Note that the |InitOracleBOU| case is missing, and the |CallOracleBOU| case
has |BoundOracleUse (suc k)| instead of |BoundOracleUse k|.  This means that if
a term of type |BoundOracleUse zero ce| can be constructed, it cannot use
|CallOracle| or |InitOracle|.  This lets us bound how much the adversary does
with the oracle.
