\section{Design Outline}
\label{sec:work}

We will now briefly present the design that we have developed so far.  This development is sufficient to represent games
featuring only a challenger and an adversary, compute the probability of an adversary winning the game, and reason about
two games having equal victory probability for the adversary.  These features suffice to represent the proof of the
One-Time Pad being secure against eavesdropping (as presented in \autoref{sec:example}), though they are not enough to prove
that the One-Time Pad is not vulnerable against a chosen plaintext attack.

% What issues are still unresolved?
% - Different notions of security: bounded by a constant, asymptotic, etc.
% - Oracles
% - Bounds on computation
% - Proof automation
% What do we need to introduce for this?
% - A syntactic monad that represents the computations.
% - A valuation for this monad.  Perhaps just note that this valuation requires us to be able to reason about
%   equalities?
% - A notion of equality of valuations.
% Other thoughts:
% - I could scrap the whole OTP example.  I suppose it's an interesting tidbit but not very useful (?)
% - 

\subsection{Agda as a Proof Assistant}

We assume that the reader is already familiar with the Agda programming language and
with the propositions-as-type approach of encoding proofs.  Briefly, when using this approach we represent a proposition
by a type, the terms of which are proofs of this proposition.  We say a proposition represented by a type |T| is true if
we can construct a term |t : T|.  We say a proposition is false if we can construct a term |nt : T -> bot|.  For the
unfamiliar reader, the Agda Wiki provides a more in-depth
introduction\footnote{\url{http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Othertutorials}}, for example
\cite{agdatut}.

When introducing game-playing proofs, we used Haskell to represent our games.  A similar construction can be used to
encode our games in Agda, with the added benefit that we can use the same language to represent properties of games and
relations between games, and to prove that these properties and relations hold.  In particular, we can express and prove
an upper bound on the advantage an adversary can have, without necessarily computing this value.

Since our primary focus lies on the representation of games and reasoning about their valuations as probability
distributions, we will not perform the underlying constructions like lists and natural numbers ourselves, instead
relying on Ulf Norell's \texttt{agda-prelude}\footnote{\url{https://github.com/UlfNorell/agda-prelude}} library for
these.  Furthermore, we assume the existence of a type representing probabilities; for example, the rational numbers
satisfy all the properties that we will require of this type.

\subsection{Games}

From the point of view of our implementation, a game is a syntactic description of the computations that will be
performed by the players.  There are a number of primitive operations provided to the players (e.g. generating a
uniformly random bitstring), and they may additionally perform any pure computations.  We can represent this kind of
structure using the free monad construction~\cite{freemonads}\cite{dtalacarte}: primitive operations are monadic
functions, sequencing of computations is done using bind, and pure computations can be included using |return|.  The
syntax for this monad is practically identical to the monad presented in \autoref{sec:proofs}.

This representation of games is easy to manipulate on, but it does not give us an immediate way to express the
probability of a game having a particular outcome.  We resolve this by defining a valuation that maps syntactic games to
a concrete monad that allows us to compute probabilities explicitly.  It is sufficient to implement this map for all the
primitive operations, and it will lift uniquely to all other terms by the universal property of the free monad.

Given a type |Q| for representing probabilities, probability distributions can be implemented as a list of pairs of
objects and their probabilities~\cite{probfunproghaskell} |List (A times Q)| or as a probability
measure~\cite{stochasticlambdacalculus} |(A -> Q) -> Q|.  Both approaches give rise to a monad: |return a| is the Dirac
distribution with value |a| and given a distribution |X| over |A| and a distribution-valued function |f : A -> B|, the
composite distribution |X >>= f| is the distribution obtained by sampling |x| from |X| and then sampling from |f x| to
obtain the result.\footnote{In fact, the first can be seen as the Writer monad transformer applied to the list monad,
while the second is a special case of the continuation monad.}

At the moment, picking a uniformly random bitstring is the only primitive operation games support, and thus the above is
sufficient to give us a valuation.  If we want further operations such as mutable state, we can implement these by
applying further monad transformers to our probability monad.  This gives us an extensible framework for formulating
more complicated games.

\subsection{One-Time Pad Revisited}

The system we have presented above is sufficient to express the One-Time Pad encryption scheme and show that it is
secure against an eavesdropper attack.  We will present how this formalisation can be performed in the system we
currently have and point out some limitations.

The following code defines types for the encryption scheme and the adversary, and specifies the game that is played.
|CryptoExpr| is our syntactic monad described in the previous section.
\begin{code}
record EncScheme : Set1 where
  constructor encscheme
  field
    Key PT CT : Set

    keygen : CryptoExpr Key
    enc : Key -> PT -> CryptoExpr CT

record SimpleEavAdv (E : EncScheme) : Set1 where
  constructor simpleeavadv
  open EncScheme E
  field 
    A1 : CryptoExpr (PT * PT)
    A2 : CT -> CryptoExpr Bool

simpleINDEAV : (E : EncScheme)(A : SimpleEavAdv E) -> CryptoExpr Bool
simpleINDEAV E A
  =  keygen                              >>= \ k 
  -> A1                                  >>= \ m
  -> coinexpr                            >>= \ b
  -> enc k (if b then fst m else snd m)  >>= \ ct
  -> A2 ct                               >>= \ b' 
  -> return (eq b b') 
  where
    open EncScheme E
    open SimpleEavAdv A
\end{code}

We can now define the One-Time Pad encryption scheme |OTP : Nat -> Scheme| and prove that it is secure by constructing a
term of the type |forall {n}(A : SimpleEavAdv (OTP n)) -> coin ==D (VAL (simpleINDEAV (OTP n) A))|.  The relation |==D|
signifies that sampling any value from the uniform distribution |coin| is equivalent to sampling it from the
distribution |VAL (simpleINDEAV (OTP n) A)|.  Since we universally quantify over the security parameter |n| and the
adversary |A : SimpleEavAdv (OTP n)|, this shows that this encryption scheme is perfectly secure.

A considerable issue with the proof is that it is inpractically long.  A step of the proof consists of specifying the
next game in the sequence and giving a proof that the two games are equivalent.  Unfortunately, these proofs often
themselves contain portions of the game, leading to a significant amount of duplication.  The following is an example of
such a step, where we argue that if the call to the adversary does not depend on the result of a coin flip, we can
postpone flipping the coin to after we call the adversary.
\begin{code}
   lbracket  uniformexpr n  >>= \ k 
   ->        A2 k           >>= \ b'
   ->        coinexpr       >>= \ b
   ->        return (eq b b') rbracket
    ==D langle congbind  (uniformexpr n)
                         (  \ k   -> A2 k      >>=
                            \ b'  -> coinexpr  >>=
                            \ b   -> return (eq b b'))
                         (  \ k   -> coinexpr  >>=
                            \ b   -> A₂ k      >>=
                            \ b'  -> return (eq b b'))
                         (  \ k   -> interchange  (A2 k) coinexpr
                                                  (\ b' b -> return (eq b b'))) rangle
   lbracket  uniformexpr n      >>= \ k
   ->        coinexpr           >>= \ b
   ->        A2 k               >>= \ b'
   ->        return (eq b b') rbracket
\end{code}

Another issue is that this proof only holds for adversaries that do not maintain state.  However, this is a limitation
in the current implementation of the framework, rather than any conceptual shortcoming of the proof.  Once stateful
games are implemented, this proof should go through mostly unchanged.
