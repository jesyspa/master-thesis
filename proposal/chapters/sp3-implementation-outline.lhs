\section{Design Outline}
\label{sec:work}

We will now briefly present the design that we have developed so far.  This development is sufficient to represent games
featuring only a challenger and an adversary, compute the probability of an adversary winning the game, and reason about
two games having equal victory probability for the adversary.  These features suffice to formalise the proof of the
One-Time Pad being secure against eavesdropping (as presented in \autoref{sec:example}), though they are not enough to prove
that the One-Time Pad is vulnerable against a chosen plaintext attack.

\subsection{Agda as a Proof Assistant}

We assume that the reader is already familiar with the Agda programming language and with the propositions-as-type
approach of encoding proofs.  Briefly, when using this approach we represent a proposition by a type, the terms of which
are seen as proofs of this proposition.  We say a proposition represented by a type |T| is true if we can construct a
term |t : T|.  We say a proposition is false if we can construct a term |nt : T -> bot|.  For the unfamiliar reader, the
Agda Wiki provides a number of more in-depth
introductions\footnote{\url{http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Othertutorials}}, for example
\cite{agdatut}.

When introducing game-playing proofs, we used Haskell to represent our games.  A similar construction can be used to
encode our games in Agda, with the added benefit that the properties of games and relations between games can not only
be expressed in it, but also shown to hold.  In particular, we can express and prove an upper bound on the advantage an
adversary can have, without necessarily computing this value.

Since our primary focus lies on the representation of games and reasoning about their valuations as probability
distributions, we will not perform the underlying constructions like lists and natural numbers ourselves, instead
relying on Ulf Norell's \texttt{agda-prelude}\footnote{\url{https://github.com/UlfNorell/agda-prelude}} library for
these.  Furthermore, we assume the existence of a type representing probabilities; since the type of rational numbers
satisfies all the properties that we will require of this type, we consider this a reasonable assumption.

\subsection{Games}

From the point of view of our implementation, a game is a syntactic description of the computations that will be
performed by the players.  There are a number of primitive operations provided to the players (e.g. generating a
uniformly random bitstring), and they may also perform any pure computations.  We can represent this kind of structure
using the free monad construction~\cite{freemonads}\cite{dtalacarte}: primitive operations are monadic operations,
sequencing of computations is done using bind, and pure computations can be included using |return|.  The syntax for
specifying a game in this monad is practically identical to the monad presented in \autoref{sec:proofs}.

This representation of games is easy to manipulate, but it does not give us an immediate way to express the
probability of a game having a particular outcome.  We resolve this by defining a valuation that maps syntactic game
descriptions to a concrete monad that allows us to compute probabilities explicitly.  It is sufficient to implement this
map for all the primitive operations, since it will lift uniquely to all other terms by the universal property of the
free monad.

Given a type |Q| for representing probabilities, probability distributions can be implemented as a list of pairs of
objects and their probabilities |List (A * Q)|~\cite{probfunproghaskell} or as a probability measure |(A -> Q) ->
Q|~\cite{stochasticlambdacalculus}.  Both approaches give rise to a monad: |return a| is the Dirac distribution with
value |a| and given a distribution |X| over |A| and a distribution-valued function |f : A -> B|, the composite
distribution |X >>= f| is the distribution obtained by sampling |x| from |X| and then sampling from |f x| to obtain the
result.\footnote{In fact, the first can be seen as the Writer monad transformer applied to the list monad, while the
second is a special case of the continuation monad.}

At the moment, picking a uniformly random bitstring is the only primitive operation games support, and thus the above is
sufficient to give us a valuation.  If we want further operations such as mutable state, we can implement these by
applying further monad transformers to our probability monad.  This gives us an extensible framework for formulating
more complicated games.

\subsection{One-Time Pad Revisited}

We will now briefly show how the One-Time Pad proof can be formalised in the system described above.  The following code
defines types for the encryption scheme and the adversary, and specifies the game that is played.  |CryptoExpr| is our
syntactic monad described in the previous section.
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

We can now define the One-Time Pad encryption scheme |OTP : Nat -> EncScheme| and prove that it is secure by
constructing a term of the type
\begin{code}
    forall {n}(A : SimpleEavAdv (OTP n)) -> coin ==D (VAL (simpleINDEAV (OTP n) A))
\end{code}
The relation |==D| signifies that sampling any value from the uniform distribution |coin| is equivalent to sampling it
from the distribution |VAL (simpleINDEAV (OTP n) A)|.  The term is constructed using essentially the same steps as we
used in the introduction, the essential steps being to show that the encryption function gives the same probability
distribution over ciphertexts and that we can make the adversary commit to a choice of |b'| before choosing |b|.  Since
we universally quantify over the security parameter |n| and the adversary |A : SimpleEavAdv (OTP n)|, this shows that
this encryption scheme is perfectly secure.

