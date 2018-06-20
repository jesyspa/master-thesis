\chapter{Intermezzo: Command Structures}
% TODO: Maybe make this nameless at some point?

As we mentioned in chapter 2, the definitions of |CryptoExpr| and |OracleExpr|
are very similar and we don't want to write them (and all the associated
instances) out explicitly.  Fortunately, we don't have to!  In this chapter
we'll show a little of what can be done.  Most of the work will be done in
\autoref{chp:interaction-structures}.  This chapter can be skipped if the reader
is only interested in the cryptographic content.

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

We will abbreviate it as |CmdStruct|.

These structures form a category with the following morphisms:
\begin{code}
record CmdMorphism (C1 C2 : CmdStruct) : Set where
  field
    CommandF   : Command C1 -> Command C2
    ResponseF  : Response C2 (CommandF c) -> Response C1 c
\end{code}

We can show this category has arbitrary products and coproducts.  We can show
that the product functor preserves arbitrary coproducts, but we haven't been
able to find an exponential object.

\section{Free Monads}

Every command structure |C| gives rise to a monad as follows:
\begin{code}
data FreeMonad : Set -> Set where
  ReturnFM : A -> FreeMonad A
  InvokeFM : (c : Command C) -> (Response c -> FreeMonad A) -> FreeMonad A
\end{code}

We will see the motivation for the name later.

We can fold over these free monads in a uniform way:
\begin{code}
CommandAlgebra : Set -> Set
CommandAlgebra R = (c : Command C) -> (Response c -> R) -> R

foldalgebra : CommandAlgebra R -> (A -> R) -> FreeMonad A -> R
foldalgebra alg f (ReturnFM a)       = f a
foldalgebra alg f (InvokeFM c cont)  = alg c (\ r -> foldalgebra alg f (cont r))
\end{code}

Note that we can regard |InvokeFM| as an algebra with result |FreeMonad R|.  We
will denote this algebra by |id-Alg|.  The instances for functor, applicative,
and monad now follow immediately:
\begin{code}
fmapFM : (A -> B) -> FreeMonad A -> FreeMonad B
fmapFM f = foldalgebra idAlg (ReturnFM . f)

apFM : FreeMonad (A -> B) -> FreeMonad A -> FreeMonad B
apFM mf ma = foldalgebra idAlg (flip fmap ma) mf

bindFM : FreeMonad A -> (A -> FreeMonad B) -> FreeMonad B
bindFM m f = foldalgebra idAlg f m
\end{code}

Much of this can be found in McBride's paper Turing-Completeness Totally Free.
A funny thing he mentions there is that this next transformation follows by the
Yoneda lemma.  Of course it does.
We can also fold over the structure in a different way, using the monadic
structure:
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
foldmonadicalgebra alg = foldalgebra (domonadisealgebra alg) return
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

\section{Interpretation}

Ignoring the previous section, we can now define what it means for a command
structure to interpret another command structure.  Well, it means we've got a
|MonadicCommandAlgebra| in that structure's free monad.  Semantically, this
means that we can simulate the first command structure with sequences of
commands from the second.  This is exactly what we want when we say we express
some interface in terms of some basic language.

Note that the coproduct here gives us a nice way of talking about two interfaces
together.  This means that we specify what operations each player can perform
and what the base language is in which they may be implemented.  We can then
construct a telescope of players, each implemented in terms of the base
operations and previous players.  Finally, we combine the implementations to get
a single implementation of all the interfaces in terms of the union of the base
languages.

This is a bit nasty to write out in Agda, but is a very neat way of modelling
things semantically, if I say so myself.

\section{Proofs of Equality}

We do still need to develop syntax for proofs of equality in this context.  This
does not seem trivial.
