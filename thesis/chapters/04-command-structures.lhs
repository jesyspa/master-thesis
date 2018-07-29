\chapter{Command Structures}
\label{chp:command-structures}

In \autoref{chp:games},  we saw the definitions of |CryptoExpr| and
|OracleExpr| and their corresponding functor and monad instances, and remarked
that they contain considerable duplication.   In this chapter we will look at
how the free monad construction can be performed in a parametrised way, allowing
us to automatically generate these types and functions over them by specifying
the operations that we want them to support.

This chapter is primarily of interest as a guide to the accompanying code.  The
ideas presented are not new; they are laid out by McBride~\cite{tctotallyfree}.
We wish to nevertheless present these constructions in some depth, as this
serves as a good introduction to the more general case we will consider in
\autoref{chp:interaction-structures}.

\section{Definition}

We have seen the following pattern in |CryptoExpr| and |OracleExpr|: one
constructor is a |Return|, while the others take a command and then a
continuation to handle a response to that command.  We start by capturing the
structure of commands and responses:

\begin{code}
record CmdStruct : Set1 where
  field
    Command   : Set
    Response  : Command -> Set
\end{code}

\section{Free Monads}

Given a command structure |C|, the corresponding free monad should have a
constructor for |Return| and a constructor for each command, taking a
continuation for its response.  We can encode this structure directly in Agda.
\begin{code}
data FreeMonad : Set -> Set where
  ReturnFM : A -> FreeMonad A
  InvokeFM : (c : Command C) -> (Response c -> FreeMonad A) -> FreeMonad A
\end{code}

The usual catamorphism construction~\cite{cataana} gives us a uniform way to
operate on these values:
\begin{code}
CommandAlgebra : Set -> Set
CommandAlgebra R = (c : Command C) -> (Response c -> R) -> R

foldalgebra : CommandAlgebra R -> (A -> R) -> FreeMonad A -> R
foldalgebra alg f (ReturnFM a)       = f a
foldalgebra alg f (InvokeFM c cont)  = alg c (\ r -> foldalgebra alg f (cont r))
\end{code}

Note that we can regard |InvokeFM| as an algebra with result |FreeMonad R|.  We
will denote this algebra by |idAlg|.  The instances for functor, applicative,
and monad now follow immediately:
\begin{code}
fmapFM : (A -> B) -> FreeMonad A -> FreeMonad B
fmapFM f = foldalgebra idAlg (ReturnFM . f)

apFM : FreeMonad (A -> B) -> FreeMonad A -> FreeMonad B
apFM mf ma = foldalgebra idAlg (flip fmap ma) mf

bindFM : FreeMonad A -> (A -> FreeMonad B) -> FreeMonad B
bindFM m f = foldalgebra idAlg f m
\end{code}

Note that return is already defined by |Return-FM|.

Put together, this allows us to extend our games with new operations without
having to define the monadic structure each time.  This is of little theoretical
interest, but makes for a more straightforward implementation.


\section{Example: Games}

Let us now consider how we can express our constructions from
\autoref{chp:games} in this manner.  We will start by taking a simplistic
but straightforward approach, and then refine it to allow for greater
flexibility.  To begin, we can define the type of commands a |CryptoExpr|
supports, and the corresponding responses, to get the |CryptoExpr| monad:
\begin{code}
data CryptoCmd : Set where
  Uniform   : Nat  ->  CryptoCmd
  GetState  :          CryptoCmd
  SetState  : ST   ->  CryptoCmd

CryptoCS : CmdStruct
Command   CryptoCS = CryptoCmd
Response  CryptoCS (Uniform n)   = BitVec n
Response  CryptoCS GetState      = ST
Response  CryptoCS (SetState _)  = top

CryptoExpr : Set -> Set
CryptoExpr = FreeMonad CryptoCS
\end{code}

Defined this way, we get the functor and monad instances of |CryptoExpr| for
free.

We can reuse |CryptoCS| to define |OracleExpr|.  Since an operation in
|OracleExpr| is either an oracle-specific operation or one of the operations
from |CryptoExpr|, we can define the command structure for oracles as a
coproduct:
\begin{code}
data OracleCmd : Set where
  InitOracle  : OracleState  -> OracleCmd
  CallOracle  : OracleArg    -> OracleCmd

OracleBaseCS : CmdStruct
Command   OracleBaseCS = OracleCmd
Response  OracleBaseCS (InitOracle _)  = OracleResult
Response  OracleBaseCS (CallOracle _)  = top

OracleCS : CmdStruct
OracleCS = CryptoCS +CS OracleBaseCS

OracleExpr : Set -> Set
OracleExpr = FreeMonad OracleCS
\end{code}

This allows us to express computations that make use of an oracle.  But in fact,
this definition tells us more: it also specifies that to implement an oracle in
the base language, we must provide an |Implementation OracleBaseCS CryptoCS|.
This plays the role of the |Oracle| type from \autoref{sec:games-oracles}.

For the sake of uniformity, we can also regard a game as a whole as an
implementation of a particularly simple command structure in terms of
|OracleCS|:
\begin{code}
GameCS : CmdStruct
Command   GameCS = top
Response  GameCS tt = Bool
\end{code}

Given an implementation of |GameCS| in terms of |OracleCS| and an implementation
of |BaseOracleCS| in terms of |CryptoCS|, we can use the fact that
implementations can be combined over coproducts to obtain an implementation of
|GameCS| in terms of the coproduct of |CryptoCS| with itself.  Since this is a
coproduct, we can take the codiagonal map, giving us an implementation of
|GameCS| in terms of |CryptoCS|, as desired.

There is a problem with this approach, namely in the usage of state.  In
\autoref{sec:games-oracles}, we had allowed for two state types, |AST| and |OST|,
for the adversary and oracle state respectively.  However, here we have used the
same type |ST|, and the composite implementation of |GameCS| in terms of
|CryptoCS| proposed above would merge the operations.  This is not the expected
behaviour.

We can rectify this by parametrising |CryptoCS| by the type, and then showing
that there is an implementation of |CryptoCS AST +CS CryptoCS OST| in terms of
|CryptoCS (AST * OST)|.  With this change in place, the composition of
implementations corresponds to the |eval| function defined in
\autoref{chp:games-oracles}.  However, unlike in the earlier development, we
have been left with no ad-hoc choices once we specified what the permitted
commands were.  We could use this technique to add further players, for example
to specify the adversary as a player explicitly, or to modify the oracle
interface, and the effects of these changes would be propagated automatically.


\section{Multiplayer Systems}
\label{sec:cs-multiplayer}

In the example above, we have seen how we can express the computations of the
challenger, adversary, and oracle as implementations of their command structures
in terms of a base language, augmented with the interfaces of the others.  We
will now generalise this situation to an arbitrary $N$-player system, where
the player at index $i$ can use the interface of the player at index $j$ iff $i <
j$.

\todo[inline]{Define coproduct}
\todo[inline]{Define implementation}
\todo[inline]{Define telescopes}

\section{Future Work}
\label{sec:cs-future-work}

\todo[inline]{Generalise an $\epsilon$-relation on a base language to work on
telescopes.}
