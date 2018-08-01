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
structure of commands and responses:\footnote{\cf{Syntactic/CommandStructure}
and \clink{Interpretation/Complete/InteractionStructure}.}

\begin{code}
record CmdStruct : Set1 where
  field
    Command   : Set
    Response  : Command -> Set
\end{code}

\section{Free Monads}

Given a command structure |C|, the corresponding free monad should have a
constructor for |Return| and a constructor for each command, taking a
continuation for its response.  We can encode this structure directly in
Agda.\footnote{\cf{Syntactic/CommandStrcuture} again, as well as
\clink{Interaction/Complete/FreeMonad}.}
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

Note that return is already defined by |ReturnFM|.

Put together, this allows us to extend our games with new operations without
having to define the monadic structure each time.  This is of little theoretical
interest, but makes for a more straightforward implementation.

\section{Example: Games}

Let us now consider how we can express our constructions from
\autoref{chp:games} using this approach.  We will start by taking a simplistic
but straightforward approach, and then refine it in \autoref{sec:cs-oracles} to
allow for greater flexibility.  To begin, we can define the type of commands a
|CryptoExpr| supports, and the corresponding responses, to get the |CryptoExpr|
monad:\footnote{\cf{Syntactic/CryptoExpr}.}
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
free.  We can repeat this construction for |OracleExpr| by adding two new
commands:\footnote{\cf{Syntactic/OracleExpr}, but note that this is not the
approach taken there.}
\begin{code}
data OracleCmd : Set where
  Uniform    : Nat          ->  OracleCmd
  GetState   :                  OracleCmd
  SetState   : ST           ->  OracleCmd
  InitOracle : OracleState  ->  OracleCmd
  CallOracle : OracleArg    ->  OracleCmd

OracleCS : CmdStruct
Command   OracleCS = OracleCmd
Response  OracleCS (Uniform n)     = BitVec n
Response  OracleCS GetState        = ST
Response  OracleCS (SetState _)    = top
Response  OracleCS (InitOracle _)  = top
Response  OracleCS (CallOracle _)  = OracleResult

OracleExpr : Set -> Set
OracleExpr = FreeMonad OracleCS
\end{code}

Being able to define |OracleExpr| this way already saves us a considerable
amount of duplication compared to our construction in \autoref{chp:games}, and
we could choose to stop here and define the gluing of oracles by hand, as we had
done earlier.  However, we may note that |OracleCmd| is an extension of
|CryptoCmd|.  This can be used to not only obtain a yet more compact
presentation, but also give a more elegant definition of the oracle
implementation type |Oracle|.

\section{Combining Command Structures}

There are two questions we need to tackle in order to define |OracleExpr| in a
more composable way: how can we combine two command structures in one, and how
can we express the implementation of one command structure in another?

We define a binary operation |+CS| on command structures that represents taking
the disjoint union of their commands, with the responses to each command staying
unchanged.  We can express this directly in
Agda:\footnote{\cf{Syntactic/CSConstructs} and
\clink{Interaction/Complete/InteractionStructure}.}
\begin{code}
_+CS_ : (C1 C2 : CmdStruct) -> CmdStruct
Command   (C1 +CS C2) = Command C1 + Command C2
Response  (C1 +CS C2) (left   c) = Response C1 c
Response  (C1 +CS C2) (right  c) = Response C2 c
\end{code}

If we regard |FreeMonad C1 A| as a term with result |A| that may use commands
from |C1|, then |FreeMonad (C1 +CS C2) A| is a term with result |A| that may use
commands from both |C1| and |C2|.  This, therefore, solves the first half of our
problem.  For the future, we remark that |_+CS_| has an identity, namely the
command structure with no commands:
%format initCS = "\D{$0^{C\!S}$}"
\begin{code}
initCS : CmdStruct
Command   initCS = bot
Response  initCS ()
\end{code}

For the second half, we need to ask what an interpretation of |C1| in |C2|
means.  A simple approach would be to map the commands of |C1| to the commands
of |C2| and map the responses in the other direction,\footnote{Although we skim
over this idea, this is in fact a very useful notion, as it gives rise to a category
of command structures.  Unfortunately, while being undeniably
\emph{interesting}, this category has not proven to be useful in any concrete
way.} but this would be too restrictive: an implementation could consist of only
a single command, rather than an arbitrary monadic term.  Instead, to implement
a command structure |C1| in terms of a command structure |C2|, we send every
command |c| of |C1| with response type |R c| to a term in the free monad of |C2|
with result |R c|.  In code, this is given
as\footnote{\cf{Syntactic/CommandStructure} and
\clink{Interaction/Complete/Implementation}.  The latter is more faithful to
this presentation.}
\begin{code}
Implementation : (C1 C2 : CmdStruct) -> Set
Implementation C1 C2 = (c : Command C1) -> FreeMonad C2 (Response C1 c)
\end{code}

This choice is in line with the development performed by
McBride~\cite{tctotallyfree} on free monads, and in fact every such
implementation of |C1| in terms of |C2| gives rise to a unique monad morphism
from |FreeMonad C1| to |FreeMonad C2|.  Moreover, we can define a function of
the following type:
%format parimpl = "\F{parallel-impl}"
\begin{code}
parimpl  : Implementation C1 C2
         -> Implementaion D1 D2
         -> Implementation (C1 +CS D1) (C2 +CS D2)
\end{code}

We invite the reader to go back and check that the |Oracle| type defined earlier
is in fact, up to isomorphism, an example of an implementation.  In the next
section, we will make this explicit.

\section{Example: Oracle Implementations}
\label{sec:cs-oracles}

Previously, we defined |CryptoCS| and |OracleCS| entirely independently.
However, the latter is an extension of the former.  Using the |_+CS_| operation
defined above, we can make this explicit in our Agda
code:\footnote{\cf{Syntactic/OracleExpr}.}
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

Defining |OracleExpr| this way gives us more information than our initial
definition: we have now made explicit that in order to implement an oracle in
terms of our base language, we must define a term of type |Implementation
OracleBaseCS CryptoCS|.  By using |parimpl| above, we can extend this to an
|Implementation OracleCS CryptoCS|, giving rise to a function |OracleExpr A ->
CryptoExpr A|.

There is a problem with this approach, namely in the usage of state.  In
\autoref{sec:games-oracles}, we had allowed for two state types, |AST| and
|OST|, for the adversary and oracle state respectively.  However, here we have
used the same type |ST|, and the implementation of |OracleCS| in terms of
|CryptoCS| proposed above would merge the operations.  This is not the expected
behaviour.

We can rectify this by parametrising |CryptoCS| by the type of the state, and
then showing that there is an implementation of |CryptoCS AST +CS CryptoCS OST|
in terms of |CryptoCS (AST * OST)|.  With this change in place, the composition
of implementations corresponds to the |eval| function defined in
\autoref{sec:games-oracles}.  However, unlike in the earlier development, we
have been left with no ad-hoc choices once we specified what the permitted
commands were.  We could use this technique to add further players, for example
to specify the adversary as a player explicitly, or to modify the oracle
interface, and the effects of these changes would be propagated automatically.


\section{Multiplayer Systems}
\label{sec:cs-multiplayer}

In the example above, we have seen how we can express the relationship between
the adversary and the oracle explicitly.  We would like to generalise this
notion to be able to represent an arbitrary $N$-player system, where player $i$
may make use of the public interface of player $j$ iff $i < j$.  This makes it
possible to specify the games in a more modular manner.  Moreover, we conjecture
that this approach can give rise to a uniform way of extending the notion of
$\epsilon$-indistinguishability on games to a similar notion on such larger
systems.

Let us start by considering the following example: how would we represent the
IND-CPA game as a four-player system, the four players being the challenger,
encryption scheme, adversary, and oracle?  It may seem strange to include
``encryption scheme'' in this list, but being able to do so easily is an
important benefit of this approach.  By phrasing the problem this way, we can
perform all the gluing of players at once, simplifying the system as a whole.

Each of the four players has the basic core language |CryptoCS|, parametrised by
their state type.  The challenger and encryption scheme are stateless, while the
adversary has state |AST| and the oracle has state |OST|.  The interfaces are as
follows:\footnote{\cf{Interaction/Complete/Example}.}
%format ChallengerCS = "\D{ChallengerCS}"
%format EncSchemeCmd = "\D{EncSchemeCmd}"
%format EncSchemeCS  = "\D{EncSchemeCS}"
%format keygen       = "\IC{keygen}"
%format encrypt      = "\IC{encrypt}"
%format AdversaryCmd = "\D{AdversaryCmd}"
%format AdversaryCS  = "\D{AdversaryCS}"
%format genmessages  = "\IC{gen-messages}"
%format guesscoin    = "\IC{guess-coin}"
\begin{code}
Command   ChallengerCS = top
Response  ChallengerCS tt = Bool

data EncSchemeCmd : Set where
  keygen   : EncSchemeCmd
  encrypt  : K -> PT -> EncSchemeCmd

Command   EncSchemeCS = EncSchemeCmd
Response  EncSchemeCS keygen         = K
Response  EncSchemeCS (encrypt _ _)  = CT

data AdversaryCmd : Set where
  genmessages  : AdversaryCmd
  guesscoin    : CT -> AdversaryCmd

Command   AdversaryCS = AdversaryCmd
Response  AdversaryCS genmessages    = PT * PT
Response  AdversaryCS (guesscoin _)  = Bool
\end{code}

We have already seen the definition of |OracleBaseCS|, which defines the oracle.
We will refer to it as |OracleCS| in this section for the sake of uniformity.

The command structures are as we would expect: the possible actions and their
arguments are captured in the command data structures, and the responses are the
result types of these action.  Having phrased it this way, we see that the types
|EncScheme| and |Adversary ST| we defined in \autoref{chp:introduction} are in
fact equivalent to
\begin{code}
FORALL st -> Implementation EncSchemeCS (CryptoExpr st)
\end{code}
and |Implementation AdversaryCS (CryptoExpr ST)| respectively.  This supports
our four-player approach: types that we had to write out explicitly in the past
are now generated for us.

Note that the command structure for the challenger has a single command that
represents running the entire game.  Represented this way, the game itself is an
implementation, rather than simply a |CryptoExpr| term.  This suggests that the
right notion of $\epsilon$-indistinguishability should be in terms of
implementations.

The implementations we need to have a complete description of the game are as
follows:
\begin{itemize}
  \item an implementation of the oracle in terms of the base language;
  \item an implementation of the adversary in terms of the oracle and the base
  language;
  \item an implementation of the encryption scheme in terms of the base
  language; and
  \item an implementation of the challenger in terms of the encryption
  scheme, adversary, and the oracle.
\end{itemize}

Since we choose the encryption scheme, it is not a problem if the encryption
scheme also has access to the adversary and the oracle: we can simply consider
encryption schemes that make no use of this access.  In code, the above thus
becomes
\begin{code}
Implementation OracleCS      (CryptoCS OST)
Implementation AdversaryCS   (CryptoCS AST  +CS OracleCS)
Implementation EncSchemeCS   (CryptoCS top  +CS AdversaryCS
                                            +CS OracleCS)
Implementation ChallengerCS  (CryptoCS top  +CS EncSchemeCS
                                            +CS AdversaryCS
                                            +CS OracleCS)
\end{code}

%format NImpl = "\D{$N$-Impl}"
%format SumCS = "\F{sum$^{C\!S}$}"
We will now define a structure that, given a list of interfaces and their
corresponding base languages, represents a list of implementations like
the above.  Such an ``$N$-player implementation'' is either an empty list, or an
implementation of the first interface in terms of the first base language and
the other interfaces, together with an $N$-player\footnote{Or, perhaps more
correctly, $(N-1)$-player.} implementation of the tails.\footnote{The full
implementation of this can be found in \clink{Interaction/Complete/Combine}.
Due to the verbosity, we only present the key ideas here.}
\begin{code}
SumCS : List CmdStruct -> CmdStruct
SumCS = foldr _+CS_ initCS

data NImpl : (infc base : List CmdStruct) -> Set where
  []    : NImpl [] []
  _::_  : {C1 D1 : CmdStruct}{CS DS : List CmdStruct}
        -> (Implementation C1 (D1 +CS sumCS CS))
        -> NImpl CS DS
        -> NImpl (C1 :: CS) (D1 :: DS)
\end{code}

Given an |NImpl CS DS|, we can construct an |Implementation (SumCS CS) (SumCS
DS)|, exactly as we wanted: in the recursive case, when |CS| is of the form |C1
:: CS'| and |DS| is of the form |D1 :: DS'|, this can be done by implementing
|C1 +CS CS'| in terms of |D1 +CS CS' +CS CS'| using the first implementation,
then merging the two occurences of |CS'|, and finally implementing |CS'| in
terms of |DS'| by recursion.

With this result, we have developed a general method of constructing types such
as |EncScheme|, |Adversary|, and |Oracle| in a manner that is independent of the
number of players involved.  While not essential for any specific example, we
feel this would be an important part of any larger system that made use of
command structures.  This is a direct generalisation of the constructs in
\autoref{chp:games}.

\section{Future Work}
\label{sec:cs-future-work}

While the notion of an $N$-player implementation is helpful in constructing
games, by itself it does not solve our problem of reasoning about games.  For
this, a comparable generalisation of the material of \autoref{chp:proofs} would
be needed.  Specifically, a way to automatically generalise a notion of
$\epsilon$-indistinguishability from the base language to an $N$-player
implementation, would be invaluable.

The primary difficulty here lies in the fact that a player may make use of a
later player's interface multiple times, making a slight change in the
implementation of the latter compound.  As we have seen in
\autoref{sec:games-constraints}, limiting the number of times an operation is
used is possible but involves constructing appropriate proof terms, which would
make the proofs even more verbose.

