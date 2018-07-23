\chapter{Command Structures}
\label{chp:command-structures}

As we mentioned in \autoref{chp:games}, the definitions of |CryptoExpr| and
|OracleExpr| are very similar and we don't want to write them (and all the
associated instances) out explicitly.  Fortunately, we don't have to!  In this
chapter we'll show how we can generate monads for representing expressions based
on the set of operations that these monads should support.

This chapter may be of interest for the practical implementation of a language
for reasoning about games, but is of no great interest theoretically.  The
notions presented are not new; they can be found in (TURING COMPLETENESS TOTALLY
FREE).  The purpose of this chapter is to serve as a prelude and motivation for
\autoref{chp:interaction-structures}, where we will study a more general version
of this construction.

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

This gives rise to a category of command structures, so we can study its
categorical structure.  This category turns out to have products and
coproducts over families indexed by a decidable set.  In practice, we only care
about the finite case.
\begin{code}
Product and coproduct placeholder
Question: general or nullary + binary?
\end{code}

The products and coproducts can be intuitively interpreted as follows: a command
in the product specifies a command for each component of the product, but only
one is executed, and its response is returned.  The command of a coproduct is a
command for one of the components, and it is always executed and gives its
response.

\section{Free Monads}

Given a command structure |C|, the corresponding expression monad should have
a constructor for |Return| and a constructor for each command, taking a
continuation for its response.  We can encode this structure directly in Agda.
\begin{code}
data FreeMonad : Set -> Set where
  ReturnFM : A -> FreeMonad A
  InvokeFM : (c : Command C) -> (Response c -> FreeMonad A) -> FreeMonad A
\end{code}

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

TODO: This section is still a very condensed version of what it should be; I
need to write out what an interpretation is and what a telescope looks like.

We will now define directly what it means for a command structure to interpret
another command structure.  TODO: Write this out formally: the idea is that we
have a |MonadicCommandAlgebra| in that structure's free monad.  Semantically,
this means that we can simulate the first command structure with sequences of
commands from the second.  This is exactly what we want when we say we express
some interface in terms of some basic language.

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

Unfortunately, this formulation quickly becomes verbose when expressed in Agda.

\section{Proofs of Indistinguishability}

TODO: Here we speak of a relation, but really we want to focus on relations
indexed by non-negative rationals.

In \autoref{chp:proofs} we have seen that although we can define a notion of
$\epsilon$-indistinguishability on games, the extension of this notion to games
with oracles involves considerable work and is specific to the signature of the
oracle involved.  In this section, we will amend this by expressing how a
relation on the free monad over some command structure |C| can be extended to a
relation over a telescope with result |C|.

Fix a sequence of interfaces |A| and a sequence of implementation languages |B|.
We will denote the coproduct of such a sequence by |Sum A|.  Since we have an
implementation of |Sum B| in |C|, we have a free monad map |f| from |FreeMonad (Sum
B)| to |FreeMonad C|.  We extend our relation by saying |a| and |b| in
|FreeMonad (Sum B)| are related if their interpretations |f a| and |f b| are
related.

KEY IDEA: Define an indistinguishability relation on implementations into |C|.

The head case is easy: if two heads are related and the tails are equal, then
the telescopes are related.  The case where the heads are identical but the
tails are not is harder, since we need to take into account that the head
implementation may use the tail implementation multiple times.


