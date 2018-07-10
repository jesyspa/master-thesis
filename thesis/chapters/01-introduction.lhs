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

\todo{Write this out}
The goal of this chapter is to introduce the problem that we are trying to
formalise.  This means that it should cover not only the basic question of what
a game is and how we reason about it, but also introduce the notion of an
oracle and the various weaker notions of security.

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
    keygen   : (FORALL st) -> CryptoExpr st K
    encrypt  : (FORALL st) -> K -> PT -> CryptoExpr st CT

record Adversary (PT CT ST : Set) : Set1 where
  field
    A1  : CryptoExpr ST (PT * PT)
    A2  : CT -> CryptoExpr ST Bool
\end{code}

We will now introduce the game itself.

\begin{code}
INDEAV  : EncScheme K PT CT -> Adversary PT CT ST
        -> CryptoExpr ST Bool
INDEAV enc adv = do
  m1 , m2 <- A1 adv
  k <- keygen enc
  b <- coin
  ct <- encrypt enc k (if b then m1 else m2)
  b' <- A2 adv ct
  return $ isYes (eq b b')
\end{code}

Now, given any encryption scheme and adversary, we have a specific stateful
non-deterministic program that we can reason about.  If that program can be
shown to be indistinguishable from a coin flip, then the encryption scheme is
secure against that adversary.  On the other hand, if the program can be shown
to be indistinguishable from |return true|, then we have found an adversary that
breaks this encryption scheme.

\section{Example: One-Time Pad (IND-EAV)}
\label{sec:intro-otp-eav}

Let us see how we can reason about a game like the one demonstrated in the
previous section.  We start by introducing our encryption scheme.  Fix an |n :
Nat|.  The scheme we use is known as the One-Time Pad, and it allows us
to encrypt $n$-bit messages using an $n$-bit key.  To generate the key, we take
an $n$-bit vector uniformly at random.  To encrypt some message $m$ with a key
$k$, we take the bitwise XOR.

\begin{code}
keygenOTP : (FORALL st) -> CryptoExpr st (BitVec n) 
keygenOTP = uniform n

encryptOTP : (FORALL st) -> BitVec n -> BitVec n -> CryptoExpr st (BitVec n)
encryptOTP key msg = return (xor key msg)

OTP : EncScheme
keygen   OTP  =  keygenOTP
encrypt  OTP  =  encryptOTP
\end{code}

We have now specified a game, and can rewrite it to show that no matter the
adversary chosen, it is indistinguishable from a coin flip.  Let us start by
writing out the game, filling in the definition of the encryption scheme:
\begin{code}
INDEAVOTP1 adv = do
  m1 , m2 <- A1 adv
  k <- uniform n
  b <- coin
  ct <- return $ xor k (if b then m1 else m2)
  b' <- A2 adv ct
  return $ isYes (eq b b')
\end{code}

First of all, we note that |k| and |b| are independent random variables and may
thus be reversed.  By the monad laws, a bind followed by a return can be written
as an |fmap|.  This gives us the following code:
\begin{code}
INDEAVOTP2 adv = do
  m1 , m2 <- A1 adv
  b <- coin
  ct <- fmap (\ k -> xor k (if b then m1 else m2)) (uniform n)
  b' <- A2 adv ct
  return $ isYes (eq b b')
\end{code}

We can show that |\ k -> xor k m| is a bijection for any |m : BitVec n|, and
since applying a bijection to a uniform distribution produces another uniform
distribution, we may omit the |fmap|, giving us the following game:
\begin{code}
INDEAVOTP3 adv = do
  m1 , m2 <- A1 adv
  b <- coin
  ct <- uniform n
  b' <- A2 adv ct
  return $ isYes (eq b b')
\end{code}

We now see that |b| and |b'| are independent random variables and can reorder
these, as well.  We can also once more rewrite a bind followed by a return as an
application of |fmap|:
\begin{code}
INDEAVOTP4 adv = do
  m1 , m2 <- A1 adv
  ct <- uniform n
  b' <- A2 adv ct
  fmap (\ b -> isYes (eq b b')) coin
\end{code}

Finally, we can show that |\ b -> isYes (eq b b'))| to be a bijection as well,
giving us the last game in the sequence:
\begin{code}
INDEAVOTP5 adv = do
  m1 , m2 <- A1 adv
  ct <- uniform n
  b' <- A2 adv ct
  coin
\end{code}

Since the outcome of |INDEAVOTP5| is independent of |adv|, it is
indistinguishable from |coin|.  We have thus shown that |OTP| is secure against
an eavesdropper attack.

\todo{Analyse this proof?}

\section{Oracles}

The above lets us reason about adversaries expressed in terms of the basic
language of non-determinsitic stateful computation.  This is useful by itself,
but by restricting adversaries to this language, we are only considering the
weakest kind of adversary possible.  If we want to strengthen our results, we
need to develop a way of expressing adversaries that may have access to
computations that cannot be expressed in this language directly.

To give an example, a straightforward strengthening of the |INDEAV| game is to
give the adversary access to the encryption function used by the challenger.
Since this computation depends on the key\footnote{Which the adversary should
\emph{not} have access to!}, this cannot be expressed directly as a
non-deterministic stateful computation by the adversary.

A function provided to the adversary in this opaque way is called an
\emph{oracle}.  Oracles have all the power that the challenger and adversary
have: they may generate random bitstrings and may read and write a state.
However, the other players cannot inspect the code or state of the oracle.  This
lets us precisely control the power of the adversary by adjusting the
information provided by the oracle.

For the moment, we will assume that there are two operations provided by the
oracle: a way to initialise the oracle state with some value of type
|OracleInit|, and a way to query the oracle function using an |OracleArg|
argument to get an  |OracleResult| response.  The types in question will depend
on the game being played.  We can represent this in code by assumpting that
|CryptoExpr| supports an additional two operations:
\begin{code}
oracleInit  : (FORALL st) ->  OracleInit  -> CryptoExpr st top
oracleCall  : (FORALL st) ->  OracleArg   -> CryptoExpr st OracleResult
\end{code}

Note that the state of the oracle is not represented in |st|: otherwise, the
adversary could use |getState| to inspect the oracle state.  We will for now
leave the oracle state hidden, and look at how it can be implemented in
\autoref{chp:games}.  We assume that only the challenger can use |oracleInit|
and only the adversary can use |oracleCall|.

We can now express a game that expresses a stronger security condition than
IND-EAV.  This is called IND-CPA, indistinguishability under chosen plaintext
attack.  The definition of an encryption scheme and an adversary remain
unchanged, so we only need to specify the game.  In this case, |OracleInit = K|,
|OracleArg = PT|, and |OracleResult = CT|.
\begin{code}
INDCPA  : EncScheme K PT CT -> Adversary PT CT ST
        -> CryptoExpr ST Bool
INDCPA enc adv = do
  m1 , m2 <- A1 adv
  k <- keygen enc
  oracleInit k
  b <- coin
  ct <- encrypt enc k (if b then m1 else m2)
  b' <- A2 adv ct
  return $ isYes (eq b b')
\end{code}

Since the |oracleInit| call happens only after |A1 adv|, the adversary cannot
effectively use the oracle when choosing the messages.  In particular, we will
show that any adversary is indistinguishable from one which does not make any
use of |oracleCall| in |A1|.

In this case, just specifying |INDCPA| is not sufficient to define the game,
since we must also define how the oracle is implemented.  The oracle state, in
this case, is |K|, since the oracle must store the encryption key used.  The
definitions are then as follows:
\begin{code}
oracleInitImpl : K -> CryptoExpr K top
oracleInitImpl = setState

oracleCallImpl : PT -> CryptoExpr K CT
oracleCallImpl pt = do
  k <- getState
  encrypt enc k pt
\end{code}

\section{Example: One-Time Pad (IND-CPA)}

Let us now show that the One-Time Pad scheme presented above is not secure with
respect to this new IND-CPA game.  As before, we fix an |n : Nat| and set |K =
CT = PT = BitVec n|.  We assume |n > 0|, since otherwise there exists only one
message of type |PT|.  Our adversary does not need to store any state, so we
choose |ST = top|.

We can now define our adversary as follows:
\begin{code}
INDCPAOTPADV : Adversary
A1 INDCPAOTPADV = return (allzero n , allone n)
A2 INDCPAOTPADV ct = do
  r <- callOracle (allzero n)
  return $ isYes (eq ct r)
\end{code}

In addition to the adversary, we must now track the definition of the oracle as
we go through the game.  In this case, we keep the same oracle definition
throughout our reasoning, but as we will see later, there are game-based proofs
where a change in the definition of the oracle is an essential part of the
proof.  We will look at the details in \autoref{chp:games}.


Let us write out |INDCPA| with |OTP| and |INDCPAOTPADV| filled in.  Note that we
can also fill in the implementation of the oracle, since we will not change it
in the future.  The purpose of separating this implementation was to restrict
the class of adversaries by ruling out adversaries that inspect the oracle.
Since we have chosen an adversary already, this purpose has been achieved, and
we do not need to retain the separation any further.  The resulting code is as
follows:
\begin{code}
INDCPAOTP1 = do
  m1 , m2 <- return $ allzero n , allone n
  k <- uniform n
  setOracleState k
  b <- coin
  ct <- return $ xor k (if b then m1 else m2)
  k' <- getOracleState
  b' <- return $ isYes (eq ct (xor k' (allzero n)))
  return $ isYes (eq b b')
\end{code}

We use |setOracleState| instead of |setState| here to disambiguate whose
state we are talking about.  Since |k| is the last value stored in the oracle
state, we know |k = k'|.  We can also inline the definitions of |m1| and |m2|.
This gives us the following game, indistinguishable from the previous:
\begin{code}
INDCPAOTP2 = do
  k <- uniform n
  b <- coin
  ct <- return $ xor k (if b then allzero n else allone n)
  b' <- return $ isYes (eq ct (xor k (allzero n)))
  return $ isYes (eq b b')
\end{code}

Since the last three operations are all returns, we can merge them into a single
operation (by the monad laws):
\begin{code}
INDCPAOTP3 = do
  k <- uniform n
  b <- coin
  missingline
\end{code}
% DOesn't compile for some reason:
% return $ isYes (eq  b (isYes (eq (xor k (if b then allzero n else allone n)) (xor k (allzero n)))))
We know that |xor k| is an injective function, so |eq (xor k v) (xor k w)| holds
iff |eq v w| holds.  We can thus simplify the above to the following:
\begin{code}
INDCPAOTP4 = do
  k <- uniform n
  b <- coin
  missingline
\end{code}
% idem: 
% return $ isYes (eq  b (isYes (eq (if b then allzero n else allone n) (allzero n))))

If |b| is |true|, then we compare |allzero n| to |allzero n| and get |true|, so
the expression as a whole is |true|.  On the other hand, if |b| is |false|, we
compare |allone n| to |allzero Nn| and get |fales|, so the expression as a whole
is |true| as well.  It follows that this game always yields |true|, and is thus
indistinguishable from |return true|.  It follows that this adversary has a
guaranteed winning strategy.

\section{Weaker Notions of Security}

Having introduced oracles to allow for the strengthening of our security
conditions, let us consider the ways in which these conditions can be weakened.
A strong motivation to look for such a weakening arises in public key
cryptography, where the adversary is given access to the public key, which is
sufficient to encrypt messages, while the challenger retains the private key,
which is used for their decryption.  The public key can often be computed from
the private key.

In this setting, the adversary may be able to do better than random by guessing
a private key and checking whether the public key corresponds to it.  If it
does, the adversary can decrypt the ciphertext and so definitely choose the
right message, while if it doesn't, he can select one at random.  If the
probability of guessing the private key correctly is $p$, then the probability
of choosing the right message is $p + \frac{1-p}{2} = \frac{1+p}{2}$, which is
slightly more than $\frac{1}{2}$.  It follows that the resulting game cannot be
indistinguishable from a coin flip.

A good first step to work around this problem is to extend the notion of
indistinguishability to identify terms that are equal up to some error
$\epsilon$.  In the above example, we can choose $\epsilon = \frac{p}{2}$ and
show that our game is $\epsilon$-indistinguishable from a coin flip.  We will
explore this weaker logic in \autoref{sec:epsilon-indistinguishability}.

However, note that this alone does not resolve the situation, since the
adversary can increase its chances of guessing the private key simply by trying
more times, potentially enumerating every possible private key to find the
correct one.  However, while this would certainly be enough to break the
encryption, such an adversary would take take time exponential in the length of
the key.

We thus extend our system in a further two ways.  First of all, we should be
able to bound the resources available to an adversary.  This includes the usual
resources of time and space, but also the number of oracle calls an adversary
can make and the bits of randomness an adversary can use.  Secondly, we should
consider not only the advantage of an adversary against a single game, but also
against a family of games indexed by a security parameter.  We will look at
these notions in \autoref{sec:security-assumptions} and
\autoref{sec:asymptotic-indistinguishability}.

Finally, many proofs in cryptography rely on assumptions that a certain problem
cannot be efficiently solved.  For example, many public key cryptography schemes
rely on the computational difficulty of prime factorisation.  However, we do not
yet have a proof that no efficient algorithm exists.  It is thus important that
our system allow for the use of such assumptions without requiring the user to
prove them.  It turns out that this is strongly related to the problem of
restricting the class of adversaries, and so we will also discuss it in
\autoref{sec:security-assumptions}.

\section{Generalised Games}

So far, we have considered a single game at a time and shown it to be
($\epsilon$-)indistinguishable to a coin flip.  A straightforward generalisation
is to take two games, both parametrised by the same adversary, and ask whether
they are ($\epsilon$-)indistinguishable.

We can phrase the previous games we have regarded in this context.  For example,
given some encryption scheme |enc| and an adversary |adv|, the statement that
|INDEAV enc adv| is indistinguishable from a coin flip is implied by the
statement that the following two games are indistinguishable:
\begin{code}
INDEAV1 enc adv = do
  m , _ <- A1 adv
  k <- keygen enc
  ct <- encrypt adv k m
  A2 adv ct

INDEAV2 enc adv = do
  _ , m <- A1 adv
  k <- keygen enc
  ct <- encrypt adv k m
  A2 adv ct
\end{code}

As before, fixing |enc|, the advantage of the adversary is the least $\epsilon$
such that these games are $\epsilon$-indistinguishable for every adversary.

\todo{Put this in a proof block?  Cut it out?}
Suppose that |INDEAV1 enc adv| and |INDEAV2 enc adv| are
$\epsilon$-indistinguishable.  We wish to show that |INDEAV enc adv| is
$\epsilon$-indistinguishable from a coin flip.  We note that by reordering
independent instructions, we can show that |INDEAV enc adv| is indistinguishable
from
\begin{code}
do
  b <- coin
  b' <- if b then INDEAV1 enc adv else INDEAV2 enc adv
  return $ isYes (eq b b')
\end{code}

Since |INDEAV1 enc adv| and |INDEAV2 enc adv| are $\epsilon$-indistinguishable,
this is $\epsilon$-indistinguishable from
\begin{code}
do
  b <- coin
  b' <- INDEAV1 enc adv
  return $ isYes (eq b b')
\end{code}
which is indistinguishable from a coin flip by the same argument as in
\autoref{sec:intro-otp-eav}.

Clasically, we can prove the converse by showing that |INDEAV1 enc adv| and
|INDEAV2 enc adv| are indistinguishable from Bernoulli distributions and showing
that the difference between the parameters of these distributions is bounded.
However, this is harder to do constructively.

By rephrasing statements about games in this way, we gain composability.  In
particular, if we wish to use a result in a further proof, it is much easier to
do so if we have shown that two games are $\epsilon$-indistinguishability,
rather than if we have shown that a game is $\epsilon$-indistinguishable from a
coin flip.

\section{Example: Pseudo-Random Functions}

Let us now consider an example that uses the notions we have introduced in this
chapter.  We would like to show that given a family of pseudorandom functions,
we can create a new family of pseudorandom functions with greater input length
by using a suitable family of hash functions.  The proof is an adaptation of the
proof given by Shoup in~\cite{gameexamples}.

Let $S$ be a finite set, $i$ and $j$ be positive integers and let
$\mathcal{F}$ be an $S$-indexed family of functions $F_s : \{0, 1\}^i \to \{0,
1\}^j$.  Let $\Gamma_{i, j}$ be the set of all functions $\{0,
1\}^i \to \{0, 1\}^j$.  We say the family $\mathcal{F}$ is pseudo-random
if it is hard to distingiuish a function taken at random from $\mathcal{F}$ from
a function taket at random from $\Gamma_{i, j}$.  Formally, this is
expressed by saying that for some negligible $\epsilon$ and any adversary |A :
(BitVec i -> BitVec j) -> Bool|, the following two games are
$\epsilon$-indistinguishable:
\begin{code}
PRFpseudo = do
  s <- random S
  A (F s)

PRFrandom = do
do
  f <- random Gammaij
  A f
\end{code}

TODO:
\begin{itemize}
  \item Rewrite this to access the function as an oracle.
  \item Define what a universal hash function is.
  \item Express a way to track a variable number of items
  \item Express a failure event step
\end{itemize}
