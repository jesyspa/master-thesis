\chapter{Interaction Structures}
\label{chp:interaction-structures}

In \autoref{chp:command-structures}, we have seen that the free monads we used
for expressing our games can be generated from a command structure.  In the
presence of indexed monads, however, command structures are no longer
sufficient: the command-response specification they provide cannot express the
indexing constraints that we would like.  In this chapter, we will show how
interaction structures~\cite{istructures, freemonads} can be used to provide a
similar construction in the indexed case.

We will focus our presentation on the differences between the two approaches.
The primary issue is that interaction structures do not typically have
coproducts, which were an essential part of our earlier construction.  We can
work around this issue by defining a different way of combining interaction
structures and use it to build the same kind of telescopes. Unfortunately, while
the results are comparable to those of command structures in theory, the
resulting code is too verbose to be of practical use.

\section{Definition}

An interaction structure is a set of states, set of commands per state, set of
responses per command, and a next state for every response.  An interaction
structure morphism sends states to states and commands to commands covariantly,
responses to responses contravariantly, and commutes with the next state map.

\begin{code}
record InteractionStructure (S : Set) : Set where
  field
    Command   : S -> Set
    Response  : {s : S} -> Command s -> Set
    next      : {s : S}(c : Command s)(r : Response c) -> S
\end{code}

We abbreviate it as |IStruct|.  The choice to make the state an index matches
with how we work with indexed monads and is more convenient when we get to
building telescopes.

Given two interaction structures, we can define what it means for one to
simulate another: basically, every command of the former has to match up with a
command in the latter.  Again, code:

\begin{code}
record ISMorphism  (IS1 : IStruct S1)(IS2 : IStruct S2)
                   (StateF : S1 -> S2) : Set where
  field
    CommandF   : Command IS1 s -> Command IS2 (StateF s)
    ResponseF  : {c : Command IS1 s}
               -> Response IS2 (CommandF c) -> Response IS1 c
    nextF      : (c : Command IS1 s)(r : Response IS2 (CommandF c))
               -> StateF (next IS1 c (ResponseF r)) == next IS2 (CommandF c) r
\end{code}

This (of course) gives rise to a category.  Yay?

\section{Constructions}

We can define a |_oplus_| construction that takes two interaction structures and
gives their combined system, with each operation changing one dimension.  This
is good when some player is implemented in terms of the instructions for A and
the instructions for B.
\begin{code}
_oplus_ : (IS1 : IStruct S1)(IS2 : IStruct S2) -> IStruct (S1 * S2)
Command   (oplus IS1 IS2) (s1 , s2) = Command IS1 s1 + Command IS2 s2
Response  (oplus IS1 IS2) {s1 , s2}  (left  c)  = Response IS1 c
Response  (oplus IS1 IS2) {s1 , s2}  (right c)  = Response IS2 c
next      (oplus IS1 IS2) {s1 , s2}  (left  c) r  = next IS1 c r , s2
next      (oplus IS1 IS2) {s1 , s2}  (right c) r  = s1 , next IS2 c r
\end{code}

This thing has a unit.  It's sometimes useful.
\begin{code}
TensorUnitIS : IStruct top 
Command   TensorUnitIS  tt  = bot
Response  TensorUnitIS  {tt} ()
next      TensorUnitIS  {tt} ()
\end{code}

We can also define a dependent version where the first component is already
aware of the state of the second, and so we can omit the second component's
state.  We denote this by |_qoplus_|.

\begin{code}
_qoplus_ : IStruct (S1 * S2) -> IStruct S2 -> IStruct (S1 * S2)
Command   (qoplus IS1 IS2) (s1 , s2) = Command IS1 (s1 , s2) + Command IS2 s2
Response  (qoplus IS1 IS2) {s1 , s2} (left  c)  = Response IS1 c
Response  (qoplus IS1 IS2) {s1 , s2} (right c)  = Response IS2 c
next      (qoplus IS1 IS2) {s1 , s2} (left  c) r = next IS1 c r
next      (qoplus IS1 IS2) {s1 , s2} (right c) r = s1 , next IS2 c r
\end{code}

\section{Free Monads}

Every interaction structure gives rise to a free indexed monad.  Maybe we can
first show that every interaction structure with |top| as state type gives rise
to a normal free monad.

In the dependent case, the code looks like this:
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
fmapFM : A => B -> FreeMonad IS A => FreeMonad IS B
fmapFM f (ReturnFM a)       = ReturnFM (f a)
fmapFM f (InvokeFM c cont)  = InvokeFM c \ r -> fmapFM f (cont r)

bindFM : A => FreeMonad IS B -> FreeMonad IS A => FreeMonad IS B
bindFM f (ReturnFM a)       = f a
bindFM f (InvokeFM c cont)  = InvokeFM c \ r -> bindFM f (cont r)
\end{code}

We have flipped the arguments of |bindFM| to emphasise the indexed structure.

There should be a forgetful inverse to this construction, the commands of which
are terms of the free monad and the results are resulting states.  At least,
that's what the interpretation stuff below would suggest.  I suspect it may run
into issues with universes, though.  Perhaps I can still show it if we assume
type-in-type, though?

\section{Interpretation}

We can now define what it means to interpret one interaction structure in
another.  This is like a morphism, but a command is mapped to a sequence of
commands.  Responses are mapped basically automatically.  In code:
\begin{code}
Implementation  : (IS : IStruct S1)(M : (S2 -> Set) -> S2 -> Set)(StateF : S1 -> S2)
                -> Set
Implementation IS M StateF
  = (c : Command IS s) -> M (StrongAtkey (Response IS c) (StateF . next IS c)) (StateF s)
\end{code}

\section{Multiplayer Systems}

There's a whole bunch of telescopes that need to be constructed in order for
multiplayer systems to work well.  The code is awful, and showing it may just
obscure the point.  Maybe draw some diagrams and refer people to the code if
they dare?
