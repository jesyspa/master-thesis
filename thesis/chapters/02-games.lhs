\chapter{Representing Games}

A game is a sequence of instructions.  Although we will later see that tracking
which player executes a given instruction can be useful later, for now we will
develop a system where this information is not preserved.

Instructions can be pure computations, but can also use randomness, state, and
call an oracle.

\section{Free Monads}

We represent games by free monads.  There are a number of types we must
parametrise over: |AdvState|, |OracleState|, |OracleArg|, |OracleResult|.  Once
we've fixed that, we can define:
\begin{code}
data CryptoExpr : Set -> Set where
  Return       : a                                                 -> CryptoExpr a
  Uniform      : (n : Nat)    -> (BitVec n      ->  CryptoExpr a)  -> CryptoExpr a
  GetAdvState  :              -> (AdvState      ->  CryptoExpr a)  -> CryptoExpr a
  SetAdvState  : AdvState     ->                    CryptoExpr a   -> CryptoExpr a
  InitOracle   : OracleState  ->                    CryptoExpr a   -> CryptoExpr a
  CallOracle   : OracleArg    -> (OracleResult  ->  CryptoExpr a)  -> CryptoExpr a
\end{code}

We can define a monad structure on this.  The instances look as follows (the
other cases are essentially the same):
\begin{code}
fmapCE : (a -> b) -> CryptoExpr a -> CryptoExpr b
fmapCE f (Return a)        = Return (f a)
fmapCE f (Uniform n cont)  = Uniform n (\ v -> fmapCE f (cont v))

bindCE : CryptoExpr a -> (a -> CryptoExpr b) -> CryptoExpr b
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

This allows us to write simple games.

\section{IND-CPA Example}

For example, the following is the IND-CPA
game of the One-Time Pad and the adversary that wins it.  We fix the security
parameter |N|.

\begin{code}
AdvState = BitVec N * BitVec N
record Adversary : Set where
  field
    A1 : CryptoExpr (BitVec N * BitVec N)
    A2 : BitVec N -> CryptoExpr Bool

OTPINDCPA : Adversary -> CryptoExpr Bool
OTPINDCPA adv = do
  key <- uniformCE N
  initOracleCE key
  msgs <- A1 adv
  b <- coinCE
  let ct = vxor key (if b then snd msgs else fst msgs)
  b' <- A2 adv ct
  return $ isYes (b == b')

OTPINDCPAADV : Adversary
A1 OTPINDCPAADV = return (allzero N , allone N)
A2 OTPINDCPAADV ct = do
  r <- callOracleCE (allone N)
  return (isYes (ct == r))
\end{code}

This approach is straightforward, but makes every adversary specification ad-hoc.

Note that this approach does not specify the implementation of oracles.
