\chapter{Interaction Structures}
\label{chp:interaction-structures}

We have seen that what we really want is a number of different languages.  So
far we have specified these by hand, but there is actually both a system to how
they are defined from basic operations, and how they relate to each other.  In
this chapter we introduce interaction structures which allow us to specify the
set of operations and the operations players provide to each other explicitly.

\section{Definition}

An interaction structure is a set of states, set of commands for each state, set
of responses for each command, next state for each response.  In code

\begin{code}
record InteractionStructure (S : Set) : Set where
  field
    Command   : S -> Set
    Response  : {s : S} -> Command s -> Set
    next      : {s : S}(c : Command s)(r : Response c) -> S
\end{code}

We abbreviate it as |IntStruct|.

Given two interaction structures, we can define what it means for one to
simulate another: basically, every command of the former has to match up with a
command in the latter.  Again, code:

\begin{code}
record ISMorphism  {S1 S2 : Set}
                   (IS1 : IntStruct S1)(IS2 : IntStruct S2)
                   (StateF : S1 -> S2) : Set where
  field
    CommandF   : {s : S1} -> Command IS1 s -> Command IS2 (StateF s)
    ResponseF  : {s : S1}{c : Command IS1 s}
               -> Response IS2 (CommandF c) -> Response IS1 c
    nextF      : {s : S1}(c : Command IS1 s)(r : Response IS2 (CommandF c))
               -> StateF (next IS1 c (ResponseF r)) == next IS2 (CommandF c) r
\end{code}

This (of course) gives rise to a category.  Yay?

\section{Constructions}

We can define a |_oplus_| construction that takes two interaction structures and
gives their combined system, with each operation changing one dimension.  This
is good when some player is implemented in terms of the instructions for A and
the instructions for B.
\begin{code}
  _oplus_ : (IS1 IS2 : InteractionStructure) -> InteractionStructure (S1 * S2)
  Command   (oplus IS1 IS2) (s1 , s2) = Command IS1 s1 , Command IS2 s2
  Response  (oplus IS1 IS2) {s1 , s2}  (left  c)  = Response IS1 c
  Response  (oplus IS1 IS2) {s1 , s2}  (right c)  = Response IS2 c
  next      (oplus IS1 IS2) {s1 , s2}  (left  c) r  = next IS1 c r , s2
  next      (oplus IS1 IS2) {s1 , s2}  (right c) r  = s1 , next IS2 c r
\end{code}

This thing has a unit.  It's sometimes useful.

We can also define a dependent version where the first component is already
aware of the state of the second, and so we can omit the second component's
state.

\section{Free Monads}

Every interaction structure gives rise to a free indexed monad.  Maybe we can
first show that every interaction structure with |top| as state type gives rise
to a normal free monad.  

TODO: Definition of the monad, fmap, bind. 

There should be a forgetful inverse to this, the commands of which are terms of
the free monad and the results are resulting states.  At least, that's what the
interpretation stuff below would suggest.  I suspect it may run into issues with
universes, though.

\section{Interpretation}

We can now define what it means to interpret one interaction structure in
another.  This is like a morphism, but a command is mapped to a sequence of
commands.  Responses are mapped basically automatically.

\section{Multiplayer Systems}

There's a whole bunch of telescopes that need to be constructed in order for
multiplayer systems to work well.
