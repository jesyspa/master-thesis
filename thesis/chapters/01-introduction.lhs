\chapter{Introduction}
\label{chp:introduction}

This thesis is structured as follows: we start by demonstrating how games can be
used in cryptography, then show how these can be represented and reasoned about
in Agda, and how common steps used in cryptography\footnote{Triple Encryption
paper} can be formalised in this manner.  We then detour into indexed monads and
interaction structures and show how these can be used to more precisely express
the computations we are interested in.  Finally, we give an overview of how
these developments could be combined in order to provide a language for
reasoning about games.

The goal of this chapter is to introduce the problem that we are trying to
formalise.  This means that it should cover not only the basic question of what
a game is and how we reason about it, but also introduce the notion of an
oracle.

\section{Motivation for Games}

In cryptography, we often wish to prove that a certain function does not exist.
The prototypical example is when we want to show an encryption scheme is secure:
we want to show that no function exists that (with high probability) correctly
decrypts messages without knowledge of the key.

Questions of this form can be rephrased as games between a challenger and an
adversary: in this case, the adversary chooses two messages, the challenger
encrypts one, and the adversary must identify which of the messages was
encrypted.  The adversary wins if he guesses correctly.  How much better the
adversary can perform than random chance is called the adversary's
\emph{advantage}, and we can now reformulate our goal from proving non-existence
to the finding of an upper bound on the advantage.

There are some games where this upper bound is clear.  For example, if the
challenger flips a coin and the adversary wins if it comes up heads, the
adversary has no active participation and so any adversary will have equal
probability of winning (and thus advantage 0).  For more complicated games, we
derive the upper bound by relating them to such simpler games.

\section{Games as Programs}

A game is a sequence of operations performed by the players, where later actions
may depend on the results of earlier actions.  We can regard this as an
imperative program, where the actions correspond to instructions, and we can use
the usual functional programming technique of encoding imperative programs using
monads to obtain a representation in Agda.

In \autoref{chp:games} we will look into the details of how these games can be
represented.  For now, let us assume that we have a |CryptoExpr ST A| type, 
monadic in |A|, with the following operations:
\begin{code}
uniform    : (n : Nat)  ->  CryptoExpr ST A (BitVec n)
coin       :                CryptoExpr ST Bool
setState   : ST         ->  CryptoExpr ST top
getState   :                CryptoExpr ST ST
\end{code}

This type represents a stateful computation with a source of randomness, and
lets us generate uniform bitvectors, flip a coin, set the state, and read from
the state.

We can now define what an encryption scheme and an adversary are in this
context.  These are parametrised over the types of the keys, plaintext messages,
ciphertext messages, and adversary state.

\begin{code}
record EncScheme (K PT CT : Set) : Set1 where
  field
    keygen  : forall {st} dot CryptoExpr st K
    enc     : forall {st} dot K -> PT -> CryptoExpr st CT

record EAVAdversary (PT CT ST : Set) : Set1 where
  field
    A1  : CryptoExpr ST (PT * PT)
    A2  : CT -> CryptoExpr ST Bool
\end{code}

We will now introduce the game itself.

\begin{code}
EAVIND  : EncScheme K PT CT -> EAVAdversary PT CT ST
        -> CryptoExpr ST Bool
\end{code}

Now, given any encryption scheme and adversary, we have a specific stateful
non-deterministic program that we can reason about.

\section{Example: One-Time Pad (IND-EAV)}

Let us see how we can reason about a game like the one demonstrated in the
previous section.  We start by introducing our encryption scheme.  Fix an |n :
Nat|.  The scheme we use is known as the One-Time Pad, and it allows us
to encrypt $n$-bit messages using an $n$-bit key.  To generate the key, we take
an $n$-bit vector uniformly at random.  To encrypt some message $m$ with a key
$k$, we take the bitwise XOR.

\begin{code}
generateKeyOTP : forall {st} dot CryptoExpr st (BitVec n) 
generateKeyOTP = uniform n

encryptOTP : forall {st} dot BitVec n -> BitVec n -> CryptoExpr st (BitVec n)
encryptOTP xkey msg = return (xor key msg)
\end{code}

This gives rise to an encryption scheme.

We can now fill in these definitions into |EAVIND|.

Then a sequence of games follows that I can't bear to write out right now.

\section{Oracles}

Sometimes, we want to give the adversary access to some extra computation they
may perform.  This is typically called an oracle.  For example, the adversary
may be given access to the encryption function.  We could give the adversary the
function explicitly.  However, some oracles are stateful: for example, they may
use a pseudo-random number generator, or store the queries already performed by
the adversary.  As such, we should not allow the adversary to get or set this
state, and want to force the adversary to use the oracle only as a black box.

As such, the adversary is given a special command that calls the oracle with an
argument and gives a result, but the adversary cannot know how this command is
implemented.  The challenger is given access to a command that sets the oracle
state.

\section{Example: One-Time Pad (IND-CPA)}

For example, the following is the IND-CPA game of the One-Time Pad and the
adversary that wins it.  We fix the security parameter |N|.  (This is the same
example as in the introduction; do we want to keep both?)

\begin{code}
AdvState = BitVec N * BitVec N
record Adversary : Set where
  field
    A1 : CryptoExpr (BitVec N * BitVec N)
    A2 : BitVec N -> CryptoExpr Bool

OTPINDCPA : Adversary -> CryptoExpr Bool
OTPINDCPA adv = do
  key <- uniformCE N
  initOracleCE key
  msgs <- A1 adv
  b <- coinCE
  let ct = vxor key (if b then snd msgs else fst msgs)
  b' <- A2 adv ct
  return $ isYes (b == b')

OTPINDCPAADV : Adversary
A1 OTPINDCPAADV = return (allzero N , allone N)
A2 OTPINDCPAADV ct = do
  r <- callOracleCE (allone N)
  return $ isYes (ct == r)
\end{code}

This approach is straightforward, but makes every adversary specification ad-hoc.
We can show that given access to an encryption oracle, the adversary has a
winning strategy against the one-time pad.

\section{Concrete and Asymptotic Security}

It is actually rather rare for an algorithm to be perfectly secure: in most
cases, if the adversary gets very lucky they can factorise our large prime, find
our discrete logarithm, etc..  However, these schemes can still be practically
useful if we can bound the probability that this happens.  Two useful classes of
such bounds are concrete and asymptotic bounds.

A concrete bound is when we show that the adversary's advantage has a specific
upper bound.

An asymptotic bound is when we show that the adversary's advantage is vanishing
as a function of some security parameter.

TODO: At some point (not here) we should note that these things often require
polynomial-time adversaries and that that isn't a constraint we can enforce in
the system as it stands.  Maybe mention something about how this can be
nevertheless `enforced' using postulates?

\section{Example: PRFs (?)}

We can show that we can extend the input size of a pseudo-random function and
get a new pseudorandom function.  This is a good example to cover because it
uses a lot of the topics we are interested in: oracles, transitions based on
failure events, adversary action reordering, oracle substitutions, bounds on
oracle uses.  It works well as motivation for why we want to study these things
later on.
