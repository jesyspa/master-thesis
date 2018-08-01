\chapter{Indexed Monads}
\label{chp:indexed-monads}

Let us return to the problem of enforcing an upper bound on the number of
times the adversary may query the oracle.  In \autoref{sec:games-constraints} we
have seen a way of imposing such a bound by defining an additional data
structure which can only be constructed if the bound is respected.  In this
chapter, we will explore an alternative approach that makes use of McBride's
notion of an indexed monad~\cite{indexedmonads}.

A major frustration with the usage of an additional datatype for imposing a
boundary on the adversary is that we must explicitly construct the proof,
despite its structure being determined by the structure of the game it refers
to.  We can avoid this by encoding the same proof information in the
|OracleExpr| type itself.  Fixing an |ST| type for the (adversary) state, we may
imagine the following datatype to work:\footnote{We have not expressed this type
explicitly, but \clink{Interaction/Indexed/Memory} gives a simpler example based
on these ideas.}
\begin{code}
data OracleExpr : Nat -> Set -> Set where
  Return      : A                                      -> OracleExpr k        A
  Uniform     : ldots  -> (ldots  ->  OracleExpr k A)  -> OracleExpr k        A
  GetState    : ldots  -> (ldots  ->  OracleExpr k A)  -> OracleExpr k        A
  SetState    : ldots  -> (ldots  ->  OracleExpr k A)  -> OracleExpr k        A
  InitOracle  : ldots  -> (ldots  ->  OracleExpr k A)  -> OracleExpr k        A
  CallOracle  : ldots  -> (ldots  ->  OracleExpr k A)  -> OracleExpr (suc k)  A
\end{code}

Indeed, a term of type |OracleExpr k A| can make at most |k| calls to the
oracle.  However, this na\"ive attempt fails to be a monad: the |CallOracle|
case of bind does not go through.  This is to be expected, since binding may
change the number of oracle calls performed.  As such, we need to extend our
notion of a monad to allow terms to have an index, and allow the bind to modify
this index.

\section{Definition}

In functional programming, we are used to the term monad referring specifically
to monads on the category of types and terms of the language we are using.
However, the mathematical definition of monad can refer to endofunctors on any
category.  The following is simply a specialisation of this definition to the
category of types and terms indexed by some type
|S|.

\begin{definition}
  Given any type |S|, the category |SetS| is the category with functions |S ->
  Set| as its objects and |S|-indexed families of functions as its morphisms.
\end{definition}

We define the morphisms in Agda as follows:
\begin{code}
_~>_ : (S -> Set) -> (S -> Set) -> Set
A ~> B = forall {s} -> A s -> B s
\end{code}

Given a function |(S -> Set) -> (S -> Set)|, we can regard it as a functor if it
has a corresponding action on morphisms.  This gives rise to the notion of an
|S|-indexed functor on |Set|, or endofunctor on |SetS|, as
follows:\footnote{\cf{Algebra/Indexed/Fuctor}.}
\begin{code}
record IxFunctor {S : Set}(F : (S -> Set) -> (S -> Set)) : Set1 where
  field
    fmapi : (A ~> B) -> (F A ~> F B)
\end{code}

Together with the usual notion of a natural transformation, this gives rise to
the category of endofunctors and natural transformations between them.  The
notion of an indexed monad now arises naturally:\footnote{\cf{Algebra/Indexed/Monad}.}
\begin{code}
record IxMonad {S : Set}(M : (S -> Set) -> (S -> Set)) : Set1 where
  field
    overlap {{ixfunctorsuper}} : IxFunctor M
    returni : A ~> M A
    joini   : M (M A) ~> M A
\end{code}

Just as with normal monads, the bind operation is of more use if our goal is to
write programs.  It can be defined in terms of |fmapi| and |joini| just as in
the non-indexed case:
\begin{code}
_bindi_ : M A s -> (A ~> M B) -> M B s
m bindi cont = joini (fmapi cont m)
\end{code}

This type signature looks a lot more familiar if we flip the order of the
arguments to get |(A ~> M B) -> (M A -> M B)|.

A useful intuition is that a term |m : M A s| is a computation that starts at
state |s| and ends at some (unknown) state |s'|.  Since |s'| is not known, the
continuation must work for \emph{any} |s'|.  This is essential to avoid the
problem we encountered when we tried to implement bind for |OracleExpr| at the
begining of the chapter.  However, on the face of it, this seems very
restrictive: in our example, this means that the continuation must work no
matter how many oracle queries may still be made.  Can it query the oracle at
all?

Fortunately, the Atkey construction~\cite{indexedmonads} can be used to work
around this limitation.

\section{The Atkey Construction}

An important feature of indexed monads is that the type of the result may depend
on the index.  That is, unlike our definition of |OracleExpr| above, the type of
an indexed monad is |(S -> Set) -> S -> Set| rather than |S -> Set -> Set|.
This means that in the call |m bindi f|, the type of values |f| operates on
depends on the index at which it is used.

The original Atkey construction~\cite{indexedmonads} makes use of this by
constructing a type that is empty except at one selected index.  This can be
defined as follows:\footnote{\cf{Algebra/Indexed/Atkey}.}
\begin{code}
data Atkey (A : Set) : S -> S -> Set where
  V : A -> Atkey A s s
\end{code}

Suppose we have an indexed monad |M|, a term |m : M (Atkey A s') s|, and a
continuation |cont : A -> M B s'|.  We can use bind as follows:
\begin{code}
m bindi \ { (V a) -> cont a }
\end{code}
In the context of the lambda, we know that the only value |Atkey A s' s''| can
attain is |V a|, and thus |s' == s''|.  The case we provided typechecks, since
|f a : M B s'|.  Since all other cases are empty, we do not have to write them
out.  The expression as a whole has type |M B s|.

There are a number of variations on this construction.  We will explore one
generalisation in particular that will come in useful later.

Suppose that we have a monadic computation that starts at an index |s| and that
yields a value of type |A|.  How can we express that given the value |a : A|
returned, we know the state |s'| that the computation ended at?  For example,
suppose that we have an oracle that may refuse queries: it returns a value of
type |Maybe OracleResult|.  If the query was refused, the number of uses does
not go down.  We know that if we query the oracle at state |suc k|, we end up in
either state |k| (if we get |just x|) or |suc k| (if we get |nothing|).  We thus
want an indexed type which contains values of the form |just x| at index |k| and
the value |nothing| at index |suc k|, and is empty elsewhere.

We can solve this using a dependent Atkey construction as follows, where |f : A
-> S| is the function that indicates the ending state for a given value |a : A|.
\begin{code}
data DepAtkey (A : Set)(f : A -> S) : S -> Set where
  DepV : (a : A){s : S} -> (pf : s == f a) -> DepAtkey A f s
\end{code}

Consider the expression |m bindi \ { (DepV a refl) -> ? }|.  Matching on the
|pf| argument lets us rewrite the type of the hole to |M B (f a)|.  It follows
that a continuation to a term |m : M (DepAtkey A f) s| corresponds to a function
|(a : A) -> M B (f a)|.

Interestingly, this type arises as the left Kan extension of the functor |const
A : A -> Set| along |f : A -> S|, where |A| and |S| are seen as discrete
categories.

\section{Oracle Query Bounds}
\label{sec:indexed-monads-bounds}

Let us return to our motivating example.  We can define the |OracleExpr| type
from above as follows:
\begin{code}
data OracleExpr (A : Nat -> Set) : Nat -> Set where
  Return      : A k                                    -> OracleExpr A k
  Uniform     : ldots  -> (ldots  ->  OracleExpr A k)  -> OracleExpr A k
  GetState    : ldots  -> (ldots  ->  OracleExpr A k)  -> OracleExpr A k
  SetState    : ldots  -> (ldots  ->  OracleExpr A k)  -> OracleExpr A k
  InitOracle  : ldots  -> (ldots  ->  OracleExpr A k)  -> OracleExpr A k
  CallOracle  : ldots  -> (ldots  ->  OracleExpr A k)  -> OracleExpr A (suc k)
\end{code}

The definitions of fmap, bind, and return all proceed like their non-indexed
counterparts.  However, the smart constructors need a change, since |Return| has
the wrong type to be a continuation for the other constructors.  Instead, we use
the Atkey construction:
\begin{code}
uniform : Nat -> OracleExpr (Atkey Nat k) k
uniform n = Uniform n \ v -> Return (V v)
\end{code}

The other smart constructors are similar, except that |callOracle| has type
|OracleArg -> OracleExpr (Atkey OracleResult k) (suc k)| to indicate that it
uses up one call to the oracle.

Effectively, we have now merged the call-counting portion of |BoundedOracleUse|
from \autoref{sec:games-constraints} into the |OracleExpr| type.  One big
benefit of this merge is that we retain this information under binding without
having to separately manipulate a proof term.  We can also extend this system to
track other properties, such as how many bits of randomness are necessary,
whether the state has been accessed, and whether the oracle has been
initialised.

Unfortunately, this solution also has some considerable drawbacks.  While we
\emph{can} keep track of many things in this way, we cannot easily choose to
track some things and ignore others, and the increasing number of type
parameters makes the code hard to read.  We will expand on what might be done
about this in \autoref{sec:indexed-monads-future-work} and
\autoref{chp:language}.

\section{Player State Types}
\label{sec:im-player-state-types}

Indexed monads can play another role in the development of games.  Recall that
we had to introduce separate notions of indistinguishability and
result-indistinguishability, since the initial and final state of the game are
not of interest to us when deciding who won.  This is rather unfortunate, as the
logic of indistinguishability is far more straightforward.

Using indexed monads we can avoid this problem by allowing the players to modify
the type of their state during execution.  This allows us to specify that a game
starts and ends with state type |top|, making the notions of
indistinguishability and result-indistinguishability coincide.  Within it, the
adversary may switch to a different type of state to store whatever information
it needs, as long as it sets the type back to |top| when it is done.

We would like to define |CryptoExpr| as follows:
\begin{code}
data CryptoExpr : (Set -> Set) -> Set -> Set where
  Return   : A s                                          -> CryptoExpr A s
  Uniform  : (n : Nat)  ->  (BitVec n -> CryptoExpr A s)  -> CryptoExpr A s
  GetState :                (s -> CryptoExpr A s)         -> CryptoExpr A s
  SetState : s'         ->  (top -> CryptoExpr A s')      -> CryptoExpr A s
\end{code}

Unfortunately, this definition does not type-check: the |Return| constructor is
polymorphic in |s : Set|, and so |CryptoExpr A s| has type |Set1|, not |Set|.
This problem can be remedied by giving |CryptoExpr| the type |(Set -> Set1) ->
Set -> Set1|, but this is very impractical.  For one, since Agda does not have
universe cumulativity, such an approach requires our Atkey constructions to
\emph{also} be in |Set1| (or universe-polymorphic), and the code quickly becomes
unmaintainable.

A more manageable solution is to define a universe |U| and an evaluation
function |eval : U -> Set|, and let |CryptoExpr| be a |U|-indexed monad.  This
has the added benefit of letting us impose constraints on state types by our
choice of |U|: for example, we can ensure that all state types have decidable
equality.

A natural question to ask is whether the state monad transformer we used in
order to define the list interpretation can be generalised to this context.
This is indeed the case: although it has the same universe size issues as
|CryptoExpr|, fixing an |S|-indexed monad |M|, some custom universe |U|, and a
function |eval : U -> Set| we can
define:\footnote{\cf{Utility/State/Indexed/FromUniverseTransformer} and other
files in that directory.}
\begin{code}
IxStateT : (U * S -> Set) -> U * S -> Set
IxStateT A (u , s) = eval u -> M (\ s' -> Sigma U \ u' -> eval u' * A (u' , s')) s
\end{code}

This code can be a little confusing due to the overloaded meaning of `state': on
the one hand, it refers to the pair |u , s| that we have on the type level, and
on the other to the values of type |eval u| that we pass around on the value
level.  To disambiguate, we will refer to the former as the `index' and to the
latter as the `message'.

The definition of |IxStateT| can then be expressed as follows: a term of
|IxStateT A (u , s)| is a function that takes a message of type |u| and returns
a monadic action in |M| at index |s| which has, as result value at index |s'|, a
new message type |u'|, a message of that type, and a value of type |A (u' ,
s')|.  If you squint, this resembles the type |U -> M (U , A)| of a non-indexed
state monad transformer.

The definition of |modify| is less complicated and makes it clear why this
approach works:
\begin{code}
modify : (eval u -> eval u') -> IxStateT (Atkey (eval u') (u' , s)) (u , s)
modify f v = return (u' , fv , V fv))
  where fv = f v
\end{code}

Here, |v| is the message.  We apply the function |f| to it, and then store the
new message type, the new message, and give as result the new message wrapped in
an Atkey.  The definitions of |get| and |set| can, fortunately, be derived from
this, and the definitions of bind and return are straightforward.

\todo[inline]{conclusion?}

\section{Interaction Structures}
% backported
\label{chp:interaction-structures}

In \autoref{chp:command-structures}, we saw a way of encoding the
command-response structure in a way that allowed us to generate the
corresponding free monad automatically.  Interaction structures allow us to do
the same in the indexed context.

Let |S| be our index type.  An interaction structure consists of a type of
commands |Command s| for each |s : S|, a type of responses |Response c| for each
command |c : Command s|, and a next state |next c r| for each |c : Command s|
and |r : Response c|.

We can implement this in
Agda:\footnote{\cf{Interaction/Indexed/InteractionStructure}.}
\begin{code}
record IStruct (S : Set) : Set where
  field
    Command   : S -> Set
    Response  : {s : S} -> Command s -> Set
    next      : {s : S}(c : Command s)(r : Response c) -> S
\end{code}

An interaction structure over a state type |S| gives rise to a free indexed
monad over |S| as follows:\footnote{\cf{Interaction/Indexed/FreeMonad}.}
\begin{code}
data FreeMonad (IS : IStruct S) : (S -> Set) -> (S -> Set) where
  ReturnFM  : A s -> FreeMonad IS A s
  InvokeFM  : (c : Command IS s) -> ((r : Response IS c)
            -> FreeMonad IS A (next IS c r))
            -> FreeMonad IS A s
\end{code}

This follows the usual pattern we have seen before: to invoke a particular
operation, we specify it (with all parameters) and then we provide a
continuation that handles the possible responses.  The fmap and bind functions
are also straightforward generalisations:

\begin{code}
fmapFM : A ~> B -> FreeMonad IS A ~> FreeMonad IS B
fmapFM f (ReturnFM a)       = ReturnFM (f a)
fmapFM f (InvokeFM c cont)  = InvokeFM c \ r -> fmapFM f (cont r)

bindFM : A ~> FreeMonad IS B -> FreeMonad IS A ~> FreeMonad IS B
bindFM f (ReturnFM a)       = f a
bindFM f (InvokeFM c cont)  = InvokeFM c \ r -> bindFM f (cont r)
\end{code}

We have flipped the arguments of |bindFM| to emphasise the indexed structure.

\section{Multiplayer Systems}

Just like in the non-indexed case, we can consider the question of how to
create an $N$-player implementation.  The essential construction does not
change, but we have to redefine the implementation and the |+CS| operation in
this context.

For the definition of |Implementation|, we need the |DepAtkey| construction we
defined earlier.  An important note here is that the structure we are
interpreting may be indexed over a different set than the structure we are
interpreting it in.  For this purpose we take the |Sf| map, which relates states
in the one to states in the
other.\footnote{\cf{Interaction/Indexed/Implementation}.}
\begin{code}
Implementation  : (IS : IStruct S1)(M : (S2 -> Set) -> S2 -> Set)(Sf : S1 -> S2)
                -> Set
Implementation IS M Sf
  = (c : Command IS s) -> M (DepAtkey (Response IS c) (Sf . next IS c)) (Sf s)
\end{code}

Note that if both |S1| and |S2| are singletons then this definition is
equivalent to the definition of |Implementation| from
\autoref{chp:command-structures}.


The definition of |+CS| in this context is more complicated.  The problem is
that in general, while |C +CS C| can be implemented in terms of |C|, this does
not carry over into the indexed case.  This can be resolved by defining two
different constructions on interaction structures, one of which is used for
combining interfaces and the other for combining base languages.

Let us start with the construction for base languages.  The essential property
we use is that our base languages do not in any way influence each other's
state.  This allows us to use the following definition, which appears to be a
straightforward generalisation of
|+CS|:\footnote{\cf{Interaction/Indexed/InteractionStructure}.}
\begin{code}
_oplus_ : IStruct S1 -> IStruct S2 -> IStruct (S1 * S2)
Command   (oplus IS1 IS2) (s1 , s2) = Command IS1 s1 + Command IS2 s2
Response  (oplus IS1 IS2) {s1 , s2}  (left  c)  = Response IS1 c
Response  (oplus IS1 IS2) {s1 , s2}  (right c)  = Response IS2 c
next      (oplus IS1 IS2) {s1 , s2}  (left  c) r  = next IS1 c r , s2
next      (oplus IS1 IS2) {s1 , s2}  (right c) r  = s1 , next IS2 c r
\end{code}

Just like the |+CS| construction, this construction has a unit, and we can fold
over this construction.  We are cheating slightly here: in reality, the argument
to |TSum| is not simply a list, since it may store elements of type |IStruct S|
for any |S|.  We correct this in the code, but the difference is not essential
here.
\begin{code}
TensorUnitIS : IStruct top 
Command   TensorUnitIS  tt  = bot
Response  TensorUnitIS  {tt} ()
next      TensorUnitIS  {tt} ()

TSum = foldr _oplus_ TensorUnitIS
\end{code}

The |_oplus_| construction defined above can be seen as taking two interaction
structures and combining their state orthogonally, so that commands that
influence one state component do not influence the other.  However, this is not
how players interact: if the oracle may be queried $n$ times and an adversary
command uses $k$ of these queries, the challenger must be aware of this.
Essentially, the state of every player must include the state of all
players that they can issue commands to.  To capture this notion, we introduce a
second operation on interaction structures denoted |_qoplus_|.  It can be seen
as the |_oplus_| operation from above with a quotient applied to the state
space.  Again, we define a fold over this operation as
well.\footnote{\cf{Interaction/Indexed/QuotientTensor}.}
\begin{code}
_qoplus_ : IStruct (S1 * S2) -> IStruct S2 -> IStruct (S1 * S2)
Command   (qoplus IS1 IS2) (s1 , s2) = Command IS1 (s1 , s2) + Command IS2 s2
Response  (qoplus IS1 IS2) {s1 , s2} (left  c)  = Response IS1 c
Response  (qoplus IS1 IS2) {s1 , s2} (right c)  = Response IS2 c
next      (qoplus IS1 IS2) {s1 , s2} (left  c) r = next IS1 c r
next      (qoplus IS1 IS2) {s1 , s2} (right c) r = s1 , next IS2 c r

QSum = foldr _qoplus_ TensorUnitIS
\end{code}

With these choices in place, we can construct $N$-player implementations as we
did before.  The Agda formulation is not enlightening, so we will not present it
here.\footnote{\cf{Interaction/Indexed/Telescope}.}  The essential point is that
just as we could use an implementation of |C1| in terms of |D1| and |SumCS CS|
and an implementation of |SumCS CS| in terms of |SumCS DS| to obtain an
implementation of |C1 +CS SumCS CS| in terms of |D1 +CS SumCS DS| in the command
structure case, here we achieve the same result, with the important distinction
that we now have two ways of combining interaction structures.  The choice that
has worked for our purposes is as follows: an implementatino of |C1| in terms of
|oplus D1 (QSum CS)| and an implementation of |QSum CS| in terms of |TSum DS|
gives an implementation of |qoplus C1 (QSum CS)| in terms of |oplus D1 (TSum
DS)|.

This gives rise to the same kind of $N$-player implementation that we already
discussed in the case of command structures in \autoref{chp:command-structures}.
In fact, this saves us a considerable amount of work: the generalisation of
simple games to games with oracles follows in its entirety from this
construction.  However, we also run into the same issue: we do not yet know how
to generalise $\epsilon$-indistinguishability from a definition on the base
language to a general definition.  As such, just like in the previous case, the
proofs of equality will necessarily be low-level compared to the expressions of
the games themselves.

\section{Future Work}
\label{sec:indexed-monads-future-work}

Indexed monads are a very powerful tool, but their verbosity and lack of
modularity makes them unappealing to use directly.  In
\autoref{sec:indexed-monads-bounds} we have seen how they can be used to
restrict what games we consider well-formed.  If we have two such constraints,
we have no way to express them separately and then enable one or both depending
on our present needs.  It would be interesting to see whether such a system
could be developed.  This could also lead to a more concise formulation of what
effect a monadic action has on the index.

Also in the oracle example, we glossed over the fact that the number of
permitted calls to the oracle does not ever increase.  As such, given an |m :
OracleExpr A k| we only need an |f : A i -> OracleExpr A i| that works for $i
\le k$, not one that works for every $i$.  This is explored by Visser \textit{et
al.}~\cite{definterp}, and appears to rely on a categorical structure on the
index set.  Expressing the conditions and resulting definition of bind
explicitly could be of interest.
