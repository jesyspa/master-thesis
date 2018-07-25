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
record CommandStructure : Set1 where
  field
    Command   : Set
    Response  : Command -> Set
\end{code}

We will abbreviate this type as |CmdStruct|.

Given two command structures |C1| and |C2|, we can speak of |C2| simulating |C1|
if for every command |c| of |C1| there is a corresponding command |c'| of |C2|,
and every response to |c'| (in |C2|) can be mapped back to a response to |c| in
|C1|.  We can express this in Agda.
\begin{code}
record CmdMorphism (C1 C2 : CmdStruct) : Set where
  field
    CommandF   : Command C1 -> Command C2
    ResponseF  : Response C2 (CommandF c) -> Response C1 c
\end{code}

This gives rise to a category of command structures and simulations between
them.  Given a type |A| with decidable equality and an |A|-indexed family of
command structures |C|, there is a product and coproduct command structure given
as follows:
\begin{code}
Product and coproduct placeholder
\end{code}

These constructions correspond to the notions of angelic and demonic
choice~\cite{indexedmonads}.   A command in the product consists of a command for
each component, and the corresponding response is a response to one of the
commands given.  A command in the coproduct, on the other hand, is a choice of
a command in one component, and the response is the response to that command.
If the index set is empty, the product (that is, the terminal object) has a
trivial command that gives no response, while the coproduct (the initial object)
has no commands.

\section{Free Monads}

Given a command structure |C|, the corresponding expression monad should have
a constructor for |Return| and a constructor for each command, taking a
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

If the result we are building has monadic structure, then we can express our
algebra in a more concise way:
\begin{code}
MonadicCommandAlgebra : (Set -> Set) -> Set
MonadicCommandAlgebra M = (c : Command) -> M (Response c)
\end{code}

We can regard the smart constructors |InvokeFM c ReturnFM| as a
|MonadicCommandAlgebra| for |FreeMonad| itself.  We can now define, for any
monad M,
\begin{code}
demonadisealgebra : MonadicCommandAlgebra M -> CommandAlgebra (M A)
demonadisealgebra alg c cont = alg c >>= cont

foldmonadicalgebra : MonadicCommandAlgebra M -> FreeMonad A -> M A
foldmonadicalgebra alg = foldalgebra (demonadisealgebra alg) return
\end{code}

This suggests the reason for the name free monad: given a monadic interpretation
of the basic commands, we can generalise it to an interpretation of a sequence
of these commands, just as given a function from the generators of a free
group, monoid, etc. we can extend it to a homomorphism on the whole group,
monoid, etc.

The |FreeMonad| construction is a functor from the category of command
structures into the category of monads on |Set|.  The action of morphisms is
\begin{code}
fmapCSMAlg : CmdMorphism C1 C2 -> MonadicCommandAlgebra C1 (FreeMonad C2)
fmapCSMAlg m c = InvokeFM (CommandF m c) \ r -> ReturnFM (ResponseF m r)

fmapCSFM : CmdMorphism C1 C2 -> FreeMonad C1 A -> FreeMonad C2 A
fmapCSFM m = foldmonadicalgebra C1 (fmapCSMAlg m)
\end{code}

There is a certain similarity between the types |CmdMorphism C1 C2| and
|MonadicCommandAlgebra C1 (FreeMonad C2)|.  The former is a way of simulating
|C1| by |C2|, where every command in |C1| maps to exactly one command in |C2|.
The latter can also be seen as a kind of simulation, but every command in |C1|
is interpreted as a sequence of commands in |C2|.  We will refer to this as an
implementation of |C1| in terms of |C2|:
\begin{code}
Implementation : (C1 C2 : CmdStruct) -> Set
Implementation C1 C2 = MonadicCommandAlgebra C1 (FreeMonad C2)
\end{code}

We can show within Agda that implementations enjoy many of the same properties
that simulations do: they give rise to another category on command structures.
Furthermore, given an implementation of |C1| in |C2| and of |D1| in |D2|, we can
combine them to obtain an implementation of the (co)product of |C1| and |D1| in
the (co)product of |C2| and |D2|.  These properties will play a crucial role in
the further development.

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
  OracleInit  : OracleState  -> OracleCmd
  OracleCall  : OracleArg    -> OracleCmd

OracleBaseCS : CmdStruct
Command   OracleBaseCS = OracleCmd
Response  OracleBaseCS (OracleInit _)  = OracleResult
Response  OracleBaseCS (OracleCall _)  = top

OracleCS : CmdStruct
OracleCS = CryptoCS +CS OracleBaseCS

OracleExpr : Set -> Set
OracleExpr = FreeMonad OracleCS
\end{code}

This allows us to express computations that make use of an oracle.  But in fact,
this definition tells us more: it also specifies that to implement an oracle in
the base language, we must provide an |Implementation OracleBaseCS CryptoCS|.
This plays the role of the |Oracle| type from \autoref{chp:games-oracles}.

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
\autoref{chp:games-oracles}, we had allowed for two state types, |AST| and |OST|,
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


\section{The Right Adjoint}

This is a technical section with little bearing on the rest of the text.  For
this section we assume type-in-type.  We consider the results morally correct
without this extension, but their formalisation is considerably more
complicated.

In the previous section, we have constructed a functor |FreeMonad| from the
category of command structures into the category of monads on |Set|.  For this
to be reasonably called a free construction, there should be some functor
|Forget| from the monads on set to command structures that is right adjoint to
|FreeMonad|.  In this section we construct this adjoint.

The definition is as follows.  Given |F : Set -> Set|:
\begin{code}
Forget : CmdStruct
Command   Forget = Sigma Set \ A -> F A
Response  Forget (A , m) = A
\end{code}

The interesting operation is how given a |CmdMorphism C (Forget M)| we can get a
morphism |forall {A} -> FreeMonad C A -> M A|:
\begin{code}
Conjugate : (cm : CmdMorphism C (Forget M)) -> FreeMonad C A -> M A
Conjugate cm (ReturnFM a) = return a
Conjugate cm (InvokeFM c cont) with CommandF cm c | graphAt (CommandF cm) c
... | B , mb | ingraph refl = mb >>= \ r -> Conjugate (cont (ResponseF cm r))
\end{code}

|graphAt| is a special function to make Agda remember that |B , mb| is the
result of |CommandF cm c|.

Now that we know that the (abstract) morphisms |FreeMonad C A -> M A| correspond
to simulations of |C| by |Forget M|, we can, if we want, work mostly with the
latter.  Pity they need type in type.

\section{Multiplayer Systems}

In the example above, we have seen how we can express the computations of the
challenger, adversary, and oracle as implementations of their command structures
in terms of a base language, augmented with the interfaces of the others.  We
will now generalis this situation to an arbitrary $N$-player system, where
the player at index $i$ can use the interface of the player at index $j$ iff $i <
j$.

TODO: Describe things properly.

Note that the coproduct here gives us a nice way of talking about two interfaces
together.  This means that we specify what operations each player can perform
and what the base language is in which they may be implemented.  We can then
construct a telescope of players, each implemented in terms of the base
operations and previous players.  Finally, we combine the implementations to get
a single implementation of all the interfaces in terms of the union of the base
languages.

ESSENTIAL IDEA (needed for next section): we have players represented by the
interfaces they provide.  Player $A_i$ is implemented in terms of its language
$B_i$ together with the coproduct of the interfaces of $A_{i+1}, A_{i+2},
\ldots$.  We can squash this together into a single implementation of the
coproduct of all $A_i$ in the coproduct of all $B_i$.  Now we implement the
coproduct of all $B_i$ in terms of some base language $C$.

\begin{theorem}
    If a telescope |T| can be interpreted in |C|, then so can every subtelescope
    of it.
\end{theorem}

\section{Future Work}

Generalise an $\epsilon$-relation on a base language to work on telescopes.
