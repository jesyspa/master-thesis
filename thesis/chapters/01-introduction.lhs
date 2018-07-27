\chapter{Introduction}
\label{chp:introduction}
%{

Cryptography plays an essential role in the modern world: we trust that
cryptographic primitives will prevent unauthorised access to our data, securing
our online activity, banking information, and whatever else we wish to keep
private.  As such, it is important to be able to verify that such primitives
provide the guarantees they promise.

A powerful tool for this verification is the technique of code-based
games~\cite{codebasedgames, gameexamples}, whereby the security condition is
formulated as a game between a \emph{challenger} and an \emph{adversary}.  The
condition is satisfied if no adversary has a high probability of winning the
game.  A typical proof proceeds by rewriting the game in ways that preserve the
probability of the adversary winning, until a direct argument for the victory
probability can be made.  We will see several examples of such proofs in this
chapter.

Given the importance that the security guarantees are satisfied, the question
arises of whether these proofs can be mechanically verified.  Several systems exist
for this purpose,
EasyCrypt\footnote{\url{http://www.easycrypt.info}} and FCF~\cite{fcf} being two
notable examples.  In this thesis, we explore how the power of dependent types,
as implemented by the Agda programming language, can be used to approach this
problem.  In particular, we show how we can define a language for games
(\autoref{chp:games}) and a logic for reasoning about this language
(\autoref{chp:proofs}).  We also remark on the models of this logic
(\autoref{chp:interpretation}), and how we can use dependent types to further
constrain the language for our purposes (\autoref{chp:indexed-monads}).  In
\autoref{chp:command-structures} and \autoref{chp:interaction-structures}, we
look at how this can be implemented in a flexible manner, and what issues arise
from a straightforward implementation in Agda.  Finally, in
\autoref{chp:language} we describe a possible design for a domain-specific
language for cryptographic proofs based on these ideas.

In this chapter, we will introduce the notion of code-based games and see what
features a proof system must have in order to be useful.

\section{Motivation for Games}
\label{sec:games-motivation}

In cryptography, we often wish to prove that no program can distinguish between
two or more possibilities.  The standard example we will use is that a good
encryption scheme should not allow an attacker to tell what message had been
encrypted, even if the set of possible messages is very small.

Following Bellare and Rogaway~\cite{codebasedgames}, we will frame questions of
this form as games between a challenger and an adversary.  The challenger
represents the system we want to prove secure, while the adversary represents an
attacker.  The challenger poses a challenge to the adversary, and the adversary
wins if it can correctly answer the challenge.  If we can show that no adversary
can reliably win the game, we conclude that our system is secure.  On the other
hand, we can prove a system to be vulnerable by exhibiting an adversary that
has a winning strategy.

An important example of a game is indistinguishability against an eavesdropper,
abbreviated IND-EAV.  The premise is that we have an encryption scheme which we
wish to prove secure against an attacker that can intercept our encrypted
messages.  The attacker wins if he can distinguish between any two encrypted
messages; we win if he cannot.

Let Alice be the challenger and Bob be the adversary.  The protocol they follow
to play the game is as follows: Bob gives Alice two messages, |m1| and |m2|.
Alice generates an encryption key and uses it to encrypt one of the messages,
chosen at random.  Alice gives Bob the resulting ciphertext and poses the
challenge: did she encrypt |m1| or |m2|?  Bob wins if his answer is correct.

Bob can definitely win half of his games, just by choosing an answer at random.
How much better Bob can do is called his \emph{advantage}.  In order to show
that an encryption scheme is secure, we must show that any adversary's advantage
is close to zero.  In order to show that a scheme is not secure, we must show
that some adversary has high advantage.

When we want to put an upper bound on the advantage, we could analyse the game
and attempt to derive this bound directly.  However, an approach that is often
simpler is to modify the game slightly and show that this change does not change
the advantage considerably.  We say that two games between which the difference
in advantage is at most $\epsilon$ are $\epsilon$-indistinguishable.  By
constructing a sequence of $\epsilon$-indistinguishable games, we can relate our
initial (complicated) game to a much simpler one, simplifying our analysis.

\section{Games as Programs}

We can regard a game as a sequence of actions performed by the players.  Players
may perform computations, generate random bits, and make use of memory.
As such, a description of a game or player can be seen as an imperative
program in a non-determinsitic, stateful programming language, the instructions
of which correspond to the actions that players may take.

Fortunately, representing imperative programs in a functional language is a
well-studied problem~\cite{monadsforfp}, and can be solved using a monad that
has operations corresponding to the imperative instructions.  We will show how
this monad can be constructed explicitly in \autoref{chp:games}.  For now, we
will assume that there is a monad |CryptoExpr ST| that supports the following
operations, where |ST| is the type of the state:
\begin{code}
uniform    : (n : Nat)  ->  CryptoExpr ST (BitVec n)
coin       :                CryptoExpr ST Bool
setState   : ST         ->  CryptoExpr ST top
getState   :                CryptoExpr ST ST
\end{code}

A term of type |CryptoExpr ST A| represents a computation that can generate
random bits and store and retrieve values of type |ST|, and that has a result of
type |A|.  We include both |uniform| and |coin| for the sake of convenience,
although one could be defined in terms of the other.

We would like to use this monad express an encryption scheme and a game between
a challenger and an adversary that expresses a security property of this scheme.
We use the same example as in \autoref{sec:games-motivation},
indistinguishability in the presence of an eavesdropper.

Let us begin by assuming that we have some type |K| for our keys, |PT| for our
plaintext messages, and |CT| for our ciphertext messages.  To define an
encryption scheme, we must give the algorithm for generating a new key and for
encrypting a message with a given key.  We can express this in Agda as a record.

\begin{code}
record EncScheme : Set1 where
  field
    keygen   : (FORALL st) -> CryptoExpr st K
    encrypt  : (FORALL st) -> K -> PT -> CryptoExpr st CT
\end{code}

We express the fact that the encryption scheme should be stateless by requiring
that it work for \emph{any} state type.  This allows us to let the adversary
choose the state type, as we will see shortly.

The adversary is given the chance to act twice during the game, first to
generate two plaintext messages, and then to guess which message had been
encrypted.  We again represent this as a record, parametrised by the type of
state |ST| that the adversary uses.

\begin{code}
record Adversary (ST : Set) : Set where
  field
    A1  : CryptoExpr ST (PT * PT)
    A2  : CT -> CryptoExpr ST Bool
\end{code}

It may seem strange that the adversary is not given access the plaintext
messages it generated earlier when it is asked to decide which was encrypted.
This is because the adversary can use |getState| and |setState| to store
these messages if it needs to.  We could have made this flow of data explicit,
but since we are modelling an imperative program that can have internal state,
this approach feels more natural.

Now we can introduce the game itself.  As before, we let the adversary pick two
messages, generate a key, encrypt one of the messages based on a coin flip,
and then let the adversary guess which one it was.  Altogether, this is a
probabilistic computation that returns |true| iff the adversary wins.

\begin{code}
INDEAV  : EncScheme -> Adversary ST -> CryptoExpr ST Bool
INDEAV enc adv = do
  m1 , m2 <- A1 adv
  k <- keygen enc
  b <- coin
  let pt = if b then m1 else m2
  ct <- encrypt enc k pt
  b' <- A2 adv ct
  return dollar (eq b b')
\end{code}

If we now fix an encryption |enc| and take an arbitrary adversary |adv|, we can
reason about the probability that evaluating |INDEAV enc adv| returns |true|.
If we can bound this probability by $\frac{1}{2}$, then we can conclude that
the encryption scheme |enc| is secure against an eavesdropper attack.  On the
other hand, if we can find an adversary that wins with high probability, we can
conclude that the scheme is vulnerable against this attack.


\section{Example: One-Time Pad (IND-EAV)}
\label{sec:intro-otp-eav}

Let us see how we can reason about a game like the one demonstrated in the
previous section.  We start by introducing our encryption scheme.  Fix an |n :
Nat|.  The scheme we use is known as the One-Time Pad, and it allows us
to encrypt $n$-bit messages using an $n$-bit key.  To generate the key, we take
an $n$-bit vector uniformly at random.  To encrypt some message $m$ with a key
$k$, we take the bitwise XOR.

\begin{code}
OTP : EncScheme
keygen   OTP  =  uniform n
encrypt  OTP  key msg = return dollar (xor key msg)
\end{code}

We can now rewrite this game to show that no matter the adversary chosen, it is
indistinguishable from a coin flip.  Let us start by writing out the game,
filling in the definition of the encryption scheme:
%format INDEAVOTP1 = "\F{IND-EAV-OTP\textsubscript{1}}"
%format INDEAVOTP2 = "\F{IND-EAV-OTP\textsubscript{2}}"
%format INDEAVOTP3 = "\F{IND-EAV-OTP\textsubscript{3}}"
%format INDEAVOTP4 = "\F{IND-EAV-OTP\textsubscript{4}}"
%format INDEAVOTP5 = "\F{IND-EAV-OTP\textsubscript{5}}"
\begin{code}
INDEAVOTP1 : Adversary ST -> CryptoExpr ST Bool
INDEAVOTP1 adv = do
  m1 , m2 <- A1 adv
  k <- uniform n
  b <- coin
  let pt = if b then m1 else m2
  ct <- return dollar (xor k pt)
  b' <- A2 adv ct
  return dollar (eq b b')
\end{code}

First of all, we note that |k| and |b| are independent random variables and may
thus be reversed.  By the monad laws, a bind followed by a return can be written
as an |fmap|.  This gives us the following code:
\begin{code}
INDEAVOTP2 adv = do
  m1 , m2 <- A1 adv
  b <- coin
  let pt = if b then m1 else m2
  ct <- fmap (\ k -> (xor k pt)) (uniform n)
  b' <- A2 adv ct
  return dollar (eq b b')
\end{code}

We can show that |\ k -> (xor k m)| is a bijection for any |m : BitVec n|, and
since applying a bijection to a uniform distribution produces another uniform
distribution, we may omit the |fmap|, giving us the following game:
\begin{code}
INDEAVOTP3 adv = do
  m1 , m2 <- A1 adv
  b <- coin
  ct <- uniform n
  b' <- A2 adv ct
  return dollar (eq b b')
\end{code}

We now see that |b| and |b'| are independent random variables and can reorder
these, as well.  We can also once more rewrite a bind followed by a return as an
application of |fmap|:
\begin{code}
INDEAVOTP4 adv = do
  m1 , m2 <- A1 adv
  ct <- uniform n
  b' <- A2 adv ct
  fmap (\ b -> (eq b b')) coin
\end{code}

Finally, we can show that |\ b -> (eq b b'))| to be a bijection as well,
giving us the last game in the sequence:
\begin{code}
INDEAVOTP5 adv = do
  m1 , m2 <- A1 adv
  ct <- uniform n
  b' <- A2 adv ct
  coin
\end{code}

Since the outcome of |INDEAVOTP5| is independent of |adv|, it is
indistinguishable from |coin|.  Since the games are indistinguishable, the
probability of drawing |true| from |INDEAVOTP1| is the same as from
|INDEAVOTP5|.  Since the advantage of any adversary against |INDEAVOTP5| is 0,
it follows that it has advantage 0 against |INDEAVOTP1| as well, and thus we
have shown that |OTP| is secure against an eavesdropper attack.

\section{Oracles}

The above lets us reason about adversaries expressed in terms of the basic
language of non-determinsitic stateful computation.  This is useful by itself,
but by restricting adversaries to this language, we are only considering the
weakest kind of adversary possible.  If we want to strengthen our results, we
need to develop a way of giving adversaries access to computations they cannot
perform themselves.

To give an example, a straightforward strengthening of the |INDEAV| game is to
give the adversary access to the encryption function used by the challenger.
Since this computation depends on the key\footnote{Which the adversary should
\emph{not} have access to!}, this cannot be expressed directly as a
computation performed by the adversary.  Instead, we must give the adversary
black-box access to the encryption function.

A function provided to the adversary in this opaque way is called an
\emph{oracle}.  Oracles have all the power that the challenger and adversary
have: they may generate random bitstrings and have access to mutable state.
However, the other players cannot inspect the code or state of the oracle.  This
lets us precisely control the power of the adversary by adjusting the
information provided by the oracle.

For the moment, we will assume that there are two operations provided by the
oracle: a way to initialise the oracle state with some value of type
|OracleState|, and a way to query the oracle function using an |OracleArg|
argument to get an  |OracleResult| response.  The types in question will depend
on the game being played.  We can represent this in code by assumpting that
|CryptoExpr| supports an additional two operations:
\begin{code}
initOracle  : OracleState  -> CryptoExpr ST top
callOracle  : OracleArg    -> CryptoExpr ST OracleResult
\end{code}

In \autoref{chp:command-structures} we will show how this approach can be
generalised to allow oracles with different signatures in a straightforward
manner.  We consider this a noteworthy feature of our system.

Note that the state of the oracle is not represented by |ST|: otherwise, the
adversary could use |getState| to inspect the oracle state.  We will for now
leave the oracle state hidden, and look at how it can be implemented in
\autoref{chp:games}.  We assume that only the challenger can use |initOracle|
and only the adversary can use |callOracle|.

We can now express a game that expresses a stronger security condition than
IND-EAV.  In IND-EAV, we assumed that the adversary could choose two messages
for the challenger to encrypt, but could not perform the encryption.  If the
adversary also has the power to encrypt messages of its choice, the game is
known as indistinguishability under a chosen plaintext attack, abbreviated
IND-CPA.  The name comes from the fact that the adversary is allowed to choose
one or more plaintext to be encrypted by the oracle.  Apart from the fact that
the challenger has to initialise the oracle and the adversary may query it, the
game is identical.

Let us now look at the code.  Since the oracle must have the key to encrypt
messages, |OracleState = K|.  The query takes a plaintext and yields a
ciphertext, so |OracleArg = PT| and |OracleResult = CT|.  The code is as
follows:
\begin{code}
INDCPA  : EncScheme -> Adversary ST
        -> CryptoExpr ST Bool
INDCPA enc adv = do
  m1 , m2 <- A1 adv
  k <- keygen enc
  initOracle k
  b <- coin
  let pt = if b then m1 else m2
  ct <- encrypt enc k pt
  b' <- A2 adv ct
  return dollar (eq b b')
\end{code}

However, we are not yet done.  Apart from specifying the interaction between the
challenger and the adversary, we must also specify the behaviour of the oracle.
Just like the challenger and adversary, the oracle may store some state, in this
case the key.  In this case, the oracle definition is straightforward:
initialisation stores the encryption key, and a query takes a plaintext message
and returns it encrypted with the stored key.  This can be expressed in code as
follows:
%format initOracleImpl = "\F{init-oracle-impl}"
%format callOracleImpl = "\F{call-oracle-impl}"
\begin{code}
initOracleImpl : K -> CryptoExpr K top
initOracleImpl = setState

callOracleImpl : PT -> CryptoExpr K CT
callOracleImpl pt = do
  k <- getState
  encrypt enc k pt
\end{code}

We have now specified the IND-CPA game, just as we had specified IND-EAV
earlier, and can reason about it in the same ways, by fixing an encryption
scheme and considering an arbitrary adversary.  Our goal is again to either
upper bound the probability of any adversary winning, or show that an adversary
exists that wins the game with certainty.

If an adversary wins the IND-EAV game against some encryption scheme |enc|, the
same adversary can win the IND-CPA game against |enc| by ignoring the oracle.
Conversely, any game that is secure against IND-CPA is also secure against
IND-EAV.  We can thus regard IND-CPA as a stronger claim about an encryption
scheme, and we will see that it is strictly stronger by showing that our
One-Time Pad scheme is not secure against it.

Before we go on, let us note that we have not specified how the implementation
of an oracle can be combined with the implementation of the game, since one has
state type |ST| and the other has state type |K|.  The full details will be
worked out in \autoref{sec:games-oracles}; for now, it suffices to remark that
we can store both at once in a state of type |ST * K|.  We will use
|getAdvState| and |getOracleState| instead of |getState| (and analogously for
|setState|) when we want to disambiguate which component we are referring to.

\section{Example: One-Time Pad (IND-CPA)}

Let us now show that the One-Time Pad encryption scheme presented above is not
secure with respect to the IND-CPA game by constructing an adversary that wins
the game with probability 1.  As before, we fix an |n : Nat| and set |K = CT =
PT = BitVec n|.  We assume |n > 0|, since otherwise there exists only one
plaintext message.

The encryption scheme can be broken using the fact that |encrypt OTP| is
deterministic.  Since the adversary has access to the encryption function, it
can use the oracle to find the ciphertext that corresponds to each message.  As
long as the two chosen messages |m1| and |m2| are distinct, the challenger chose
to encrypt |m1| iff the given ciphertext is equal to the ciphertext of |m1|.

In code, we need to choose two specific messages.  Let |allzero n| and |allone
n| be the $n$-bit vectors that consist entirely of zeroes and ones respectively.
They are distinct, since |n > 0|.  To decide which message the challenger chose to
encrypt, we query the oracle to encrypt |allzero n|, and respond with |true| iff
this is equal to the given ciphertext.

This can be expressed in Agda as follows.  Note that since we have chosen our
messages a priori, we do not need to store any state, and can choose |ST = top|.
%format INDCPAOTPADV = "\F{IND-CPA-OTP-ADV}"
\begin{code}
INDCPAOTPADV : Adversary top
A1 INDCPAOTPADV = return (allzero n , allone n)
A2 INDCPAOTPADV ct = do
  r <- callOracle (allzero n)
  return dollar (eq ct r)
\end{code}

The attentive reader will notice that this kind of attack will work on any
deterministic encryption scheme.  We only present this special case, since the
general proof involves an encoding of determinism in Agda.

Let us write out |INDCPA| with |OTP|, |INDCPAOTPADV|, and the definition of the
oracle filled in.  As we mentioned, the combination of the adversary and oracle
state results in the state type being |top * K|.

It may seem strange to go to such lengths to define the oracle separately, only
to immediately inline it when we begin with the proof.  However, recall that the
purpose of the separation was to prevent the adversary from accessing the oracle
state.  Since we have chosen an adversary that does not does this, the
separation does not play any further role in this case.

The resulting code is as follows:
%format INDCPAOTP1 = "\F{IND-CPA-OTP\textsubscript{1}}"
%format INDCPAOTP2 = "\F{IND-CPA-OTP\textsubscript{2}}"
%format INDCPAOTP3 = "\F{IND-CPA-OTP\textsubscript{3}}"
%format INDCPAOTP4 = "\F{IND-CPA-OTP\textsubscript{4}}"
%format INDCPAOTP5 = "\F{IND-CPA-OTP\textsubscript{5}}"
\begin{code}
INDCPAOTP1 : CryptoExpr (top * K) Bool
INDCPAOTP1 = do
  m1 , m2 <- return dollar allzero n , allone n
  k <- uniform n
  setOracleState k
  b <- coin
  let pt = if b then m1 else m2
  ct <- return dollar (xor k pt)
  k' <- getOracleState
  b' <- return dollar (eq ct (xor k' (allzero n)))
  return dollar (eq b b')
\end{code}

We use |setOracleState| instead of |setState| here to disambiguate whose
state we are talking about.  Since |k| is the last value stored in the oracle
state, we know |k = k'|.  We can also inline the definitions of |m1| and |m2|.
This gives us the following game, indistinguishable from the previous:
\begin{code}
INDCPAOTP2 = do
  k <- uniform n
  b <- coin
  let pt = if b then m1 else m2
  ct <- return dollar (xor k pt)
  b' <- return dollar (eq ct (xor k (allzero n)))
  return dollar (eq b b')
\end{code}

By the monad laws, we can rewrite this game as follows, translating |return|
statements into |let| bindings and inlining the definition of |ct|:
\begin{code}
INDCPAOTP3 = do
  k <- uniform n
  b <- coin
  let  pt  = if b then allzero n else allone n
       b'  = (eq (xor k pt) (xor k (allzero n)))
  return dollar (eq b b')
\end{code}

We know that |xor k| is an injective function, so |eq (xor k v) (xor k w)| holds
iff |eq v w| holds.  We can thus simplify the above to the following:
\begin{code}
INDCPAOTP4 = do
  k <- uniform n
  b <- coin
  let  pt  = if b then allzero n else allone n
       b'  = (eq pt (allzero n))
  return dollar (eq b b')
\end{code}

If |b| is |true|, then we compare |allzero n| to |allzero n| and get |true|, so
the expression as a whole is |true|.  On the other hand, if |b| is |false|, we
compare |allone n| to |allzero n| and get |false|, so the expression as a whole
is |true| as well.  It follows that this game always yields |true|, and so this
adversary is guaranteed to win it.

\section{Weaker Notions of Security}
\label{sec:intro-weaker}

Having introduced oracles to allow for the strengthening of our security
conditions, let us consider the opposite problem: in what ways can a security
condition be weakened?

A strong motivation to look for such variations arises in public key
cryptography.  Instead of generating a single key that is used for both
encryption and decryption, a public key encryption scheme generates a public key
that can be used for encrypting messages and a private key that is needed to
decrypt them.  As the name suggests, the public key is available to both the
challenger and adversary, while only the challenger has the private key.

In this setting, the adversary can guess a private key and check whether it
corresponds to the challenger's public key.  This improves the advantage of the
adversary somewhat, since the private key makes it possible to decrypt the
message.  If the adversary is allowed to attempt this repeatedly, then the
advantage will compound.  Neverthelesss, public key cryptography is effective in
practice: this is because the probability of guessing the private correctly is
so small, the adversary would have to make a very large number of attempts,
making the attack impractical.

It is thus desirable to be able to express bounds on the resources an adversary
may use.  We will see a simple form of this in \autoref{sec:games-constraints},
where we will show how we can bound the number of oracle queries an adversary
makes.

In practice, we generally cannot say that an attacker will be able to perform at
most some number of queries.  Instead, some encryption schemes allow the user to
choose the key length they want, letting them increase security as necessary.
In this setting, we want to show that the advantage of the adversary can be made
arbitrarily small as the key length goes to infinity.  This also suggests a
new class of constraints on the adversary: we can require that the adversary
only uses an amount of resources polynomial in the key length.

Finally, arguments in cryptography often rely on conjectures such as $P \neq
NP$.  In order to be able to formalise these arguments we need to be able to
represent these conjectures, and it turns out that this question is highly relevant
to the question of asymptotic bounds.

Ensuring that the above notions can be represented within the system we design
was an important constraint for us.  We will discuss how we achieve them in
detail in \autoref{sec:security-assumptions}, but they are worth keeping in mind
throughout the development.

\section{Generalised Games}
\label{sec:intro-general-games}

We will finish this chapter by slightly generalising the kind of argument we
would like to be able to make.  So far, we have always considered a single game
as our starting point, and argued that the adversary cannot win at this game.
However, as the word ``indistinguishability'' suggests, the situation we are
interested in is somewhat more general: given two games, is there any adversary
that can distinguish between the two?

The benefit of this formulation is that a claim phrased this way is much easier
to reuse in a portion of another game.  If we know that no adversary can
distinguish between games |X| and |Y|, then we can replace |X| by |Y| in the
context of another game and know that this is a sound rewriting step.  This also
relates to the question of how we can express security assumptions that we
discussed in the previous section.

The games we have seen so far can all be expressed in this manner.  In the case
of IND-EAV and IND-CPA, instead of asking whether the adversary can tell which
message was encrypted, we ask whether the adversary can tell whether they are
in a game where the challenger always encrypts the first message, or in a game
where the challenger always encrypts the second message.  These two games that
correspond to IND-EAV are as follows:
%format INDEAV1 = "\F{IND-EAV\textsubscript{1}}"
%format INDEAV2 = "\F{IND-EAV\textsubscript{2}}"
\begin{code}
INDEAV1 : EncScheme -> Adversary ST -> CryptoExpr ST Bool
INDEAV1 enc adv = do
  m , _ <- A1 adv
  k <- keygen enc
  ct <- encrypt adv k m
  A2 adv ct

INDEAV2 : EncScheme -> Adversary ST -> CryptoExpr ST Bool
INDEAV2 enc adv = do
  _ , m <- A1 adv
  k <- keygen enc
  ct <- encrypt adv k m
  A2 adv ct
\end{code}

If an adversary |adv| can distinguish between |INDEAV1 enc| and |INDEAV2 enc|
for some encryption scheme |enc|, then we can construct an adversary that
reliably wins |INDEAV enc| by noting that |INDEAV| can be rewritten as the
following game:
%format INDEAVp = "\F{IND-EAV'}"
\begin{code}
INDEAVp : EncScheme -> Adversary ST -> CryptoExpr ST Bool
INDEAVp enc adv = do
  b <- coin
  b' <- if b then INDEAV1 enc adv else INDEAV2 enc adv
  return dollar b == b'
\end{code}

As such, this really is a generalisation of the notion of games we had
considered up to this point.

This concludes our exploration of the problem space.  We have seen that to
express game-based proofs we need to be able to represent games, and need some
set of rules specifying when two games are $\epsilon$-indistinguishable.  If we
wish to express stronger security guarantees then our system must support the
use of oracles, while expressing weaker guarantees requires a way of imposing
constraints on the class of adversaries.  In the next two chapters we will lay
out the groundwork of our system, and in the rest of this thesis we will show
various ways in which it can be refined.

%}
