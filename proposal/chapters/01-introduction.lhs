\section{Introduction}
\label{chp:introduction}

Cryptographic algorithms are ubiqutous in the modern world, and it is thus important that we can be certain they satisfy
the security guarantees they claim to provide; it is thus of value to be able to automatically verify that such proofs
are correct.  To facilitate this, we aim to develop a framework in which cryptographic algorithms and proofs about them
can be expressed.

A number of such frameworks, such as EasyCript\footnote{\url{www.easycrypt.info}} and FCF~\cite{fcf}, already exist.  Our
approach is novel in that we use the Agda programming language, which allows us to employ the power of dependent types
in our solution.  In particular, this allows us to express invariants of the algorithm that cannot be expressed in
simpler languages.

We will focus on cryptographic proofs expressed in a game-based manner~\cite{codebasedgames}.  In this setting, a
problem is framed as a game between a \emph{challenger} and an \emph{adversary}.  The challenger represents the
cryptographic algorithm in question, while the adversary represents an attempt to circumvent the security.  An upper
bound on the probability that any adversary wins the game thus corresponds to a statement about the security of this
algorithm.  A proof of such an upper bound typically involves making small modifications to the game, bounding the
difference in victory probability introduced in each, until we arrive at a game where the probability of the adversary
winning is clear.

In this setting, the game, challenger, and adversary are all non-deterministic computations with access to some basic
functionality such as random number generation.  Our approach is to syntactically represent these computations in a free
monad\footnote{Good citation?} and then give these terms a valuation in some monad for stateful non-determinsitic
computation, in which we can compute the probability of a certain outcome\cite{probfunproghaskell}.  By giving an upper
bound on how the total probability is affected by modifications of the syntactic description, we can develop set of
valid rewriting rules.

The syntactic approach we adopt allows us to limit what computations the challenger and adversary can perform: for
example, we can guarantee that the adversary does not inspect the state of the challenger (or vice-versa) by ruling such
access out on the type level.\todo{This feels a bit incomplete; say something about not computing the valuation?}

There are still a number of issues that we must address in the remainder of the research.  While we have already found a
set of combinators\todo{Better word?} that can be used to show that two games are identical, we have yet to develop a
comparable system for showing that two games are merely very similar.  Furthermore, many existing games involve the
adversary having access to some stateful \emph{oracle}, which can be queried for further information.  We do not yet
know how to represent such oracles within our system, or how to bound the number of times an oracle may be used.

We have been able to formalise a proof of the security of the one-time pad encryption scheme against eavesdropper
attacks within our system.  However, even the proof of such a short problem is inconveniently long, and we would like to
research the possibility of using reflection and proof search to reduce the amount of duplication inherent to it.

In the remainder of this proposal, we will introduce cryptographic proofs using games via an informal example
(Section~\ref{sec:example}), give an overview of the construction performed so far (Section~\ref{sec:work}), and go in
more detail on what we hope to achieve in the remainder (Section~\ref{sec:plans}).

\section{Encryption Schemes}

An \emph{encryption scheme} is a tuple $\sigma = (K, M_p, M_c, e, d)$ where $K$ and $M_p$ are finite sets\footnote{The
assumption that $M_p$ is finite is not essential, but makes the development easier.}, $e : K \times M_p \to M_c$, $d : K
\times M_c \to M_p$ and for any $k \in K$ and $m \in M_p$, $d(k, e(k, m)) = m$.  We can regard $K$ as the set of keys,
$M_p$ and $M_c$ as the sets of plaintext and ciphertext messages, and $e$ and $d$ as the encryption and decryption
functions.  We allow $e$ and $d$ to be non-deterministic functions.

We say that an encryption scheme $\sigma$ is \emph{secure} iff for any (non-deterministic) function $f : M_c \to M_p$,
the probability that $f(e(k, m)) = m$ with $k$ sampled uniformly from $K$ and $m$ sampled uniformly from $M_p$ is
$\abs{M_p}^{-1}$.  In other words, any function $f$ that does not depend on the choice of key does no better a job of
decrypting a ciphertext produced with this scheme than simply selecting a plaintext at random would, which gives the
correct plaintext with probability $\abs{M_p}^{-1}$.

Showing that an encryption scheme is secure involves reasoning about an arbitrary function $f$, which can be difficult
and error-prone.  \todo{Explain why this is difficult.} However, note that if $m_0, m_1 \in M_p$ with $m_0 \neq m_1$,
then for every $f : M_c \to M_p$, the probability that $f(e(k, m)) = m$ with $k$ chosen uniformly from $K$ and $m$
chosen uniformly from $\{m_0, m_1\}$ is $\frac 1 2$.  If this were not so, then $f$ could return a uniformly random $m
\in M_p$ for inputs other than $e(k, m_0)$ and $e(k, m_1)$ and choose better than random for inputs of that form.  On
the other hand, if the adversary cannot distinguish between the ciphertexts of any two particular messages, then it
certainly cannot decode any ciphertext.
\todo{Comment on why we want this reformulation.}

We thus reformulate the condition as follows: an encryption scheme $\sigma$ is \emph{secure} iff for any probability
distribution $D$ on $M_p \times M_p$ and any function $f : M_p \times M_p \times M_c \to \{0, 1\}$, the probability that
$f(m_0, m_1, e(k, m_b)) = b$ with $(m_0, m_1)$ sampled from $D$, $k$ sampled uniformly from $K$, and $b$ sampled
uniformly from $\{0, 1\}$ is exactly $\frac 1 2$.

It seems that we have not much advanced towards our goal, since we must still argue about an arbitrary function $f$.
However, by reformulating this problem as an interaction between a \emph{challenger} and an \emph{adversary} we can use
game-playing techniques~\cite{gameplayingproofs} to more easily reason about the problem.

\subsection{Games as Security Conditions}

We will now define our first game, typically called indistinguishability under eavesdropping, abbreviated IND-EAV, as an
interaction protocol between two parties, the \emph{challenger} and the \emph{adversary}.  The challenger performs a
fixed set of computations which define the game.  The adversary must conform the protocol, but can otherwise perform any
computations.

The game, parametrised by the encryption scheme $\sigma = (K, M_p, M_c, e, d)$, is defined as follows:
\begin{enumerate}
    \item The challenger chooses a key $k \in K$ uniformly at random.
    \item The adversary chooses two messages $m_0, m_1 \in M_p$ and gives them to the challenger.
    \item The challenger chooses $b \in \{0, 1\}$ uniformly at random.
    \item The challenger encrypts $m_b$ with key $k$ and gives the result, $c = e(k, m_b)$ to the adversary.
    \item The adversary returns $b'$.
\end{enumerate}
We say that the adversary \emph{wins} the game iff $b = b'$.  We say that the \emph{EAV-IND$_\sigma$ advantage} of an
adversary that wins with probability $p$ is $\abs{p-0.5}$.  We may omit the game or encryption scheme when it is clear
from the context.

It may seem more natural to define the advantage as $p$ or as $p-0.5$.  However, given an adversary |adv| that wins with
probability $p < 0.5$ we can construct an adversary |adv'| that wins with probability $p' > 0.5$: simply simulate $A$ in
order to obtain the two messages and get $b'$, then return $\neg b'$.  Since |adv'| wins whenever |adv| loses, the
probability $p'$ is $1-p > 0.5$, as desired.  The existence of a worse-than-random adversary is thus as much evidence of
the scheme being insecure as the existence of a better-than-random adversary.

Reformulating the security condition once again, we say that an encryption scheme $\sigma$ is \emph{strictly secure
against eavesdropping} if for any adversary |adv| the EAV-IND$_\sigma$ advantage of |adv| is zero.

\section{Games as Programs}

So far, we have relied on the reader's intuitive understanding of the notion of a non-deterministic function to define
the possible actions of the challenger and the adversary.  Our goal, however, is to reason about these security notions
in a proof assistant, which requires a more rigorous definition of each game.  We will now show how these games can be
defined in Haskell.  This differs somewhat from the representation we will use in Agda, but conveys the general idea.

We regard the game as a computation in some |Game| monad, parametrised by the state used by the adversary and the result
of the game.  Computations performed by the challenger are known, so they can be directly encoded in the program.
Computations performed by the encryption scheme and adversary are given as parameters to the program.  We then have the
following code:
%{
%format :: = "::"
%format forall = "\forall\hspace{-0.25em}"

%format Int = "\D{Int}"

%format BitVector = "\D{BitVector}"
%format EAV_Adversary = "\D{EAV\hspace{-0.15em}\_Adversary}"
%format Game = "\D{Game}"
%format generateKey = "\RF{generateKey}"
%format encrypt = "\RF{encrypt}"
%format chooseMessages = "\RF{chooseMessages}"
%format chooseOutcome = "\RF{chooseOutcome}"

%format eav_game = "\F{eav\hspace{-0.1em}\_game}"
%format generateKeyOTP = "\F{generateKeyOTP}"
%format encryptOTP = "\F{encryptOTP}"
%format otp_game = "\F{otp\_game}"

%format flipCoin = "\F{flipCoin}"
%format uniform = "\F{uniform}"

%format m0 = "m_0"
%format m1 = "m_1"

%format otp_game1 = "\F{otp\_game1}"
%format otp_game2 = "\F{otp\_game2}"
%format otp_game3 = "\F{otp\_game3}"
%format otp_game4 = "\F{otp\_game4}"

\begin{code}
data EncScheme key pt ct = EncScheme
  { forall as dot generateKey  ::               Game as key
  , forall as dot encrypt      :: key -> pt ->  Game as ct
  }

data EAV_Adversary as pt ct = EAV_Adversary
  { chooseMessages  ::        Game as (pt comma pt)
  , chooseOutcome   :: ct ->  Game as Bool
  }

eav_game :: EncScheme key pt ct -> EAV_Adversary as pt ct -> Game as Bool
eav_game enc adv = do
    k              <- generateKey enc
    (m0 comma m1)  <- chooseMessages adv
    b              <- flipCoin
    m'             <- encrypt enc k (if b then m1 else m0)
    b'             <- chooseOutcome adv m'
    return (eq b b')
\end{code}

The adversary state |as| is not used directly in this code, but we assume the adversary can put and get values of type
|as| as a monadic action, similarly to the |State as| monad.  We can thus imagine that the adversary may store the two
messages prior to returning them from |chooseMessages|, and then later get them in |chooseOutcome| in order to compute
the outcome.  Of course, since the adversary may choose any type |as|, it may store any info it wishes to.  On the other
hand, since all actions of the challenger must be valid for any choice of |as|, we know by parametricity that the
challenger cannot inspect this state.\footnote{Strictly speaking, this is not true for Haskell, since the challenger
could set the state to |undefined|.  However, this problem does not arise in Agda.}

Both the challenger and the adversary have access to the |flipCoin : Game as Bool| operation, which allows them to
perform non-deterministic computations.  For convenience, we also assume that there is a |uniform : Int -> Game as
BitVec| that provides a given number of bits of randomness at once.

\section{Indistinguishable Games}

%{
%format g0 = "g_0"
%format g1 = "g_1"

%format gameA = "\F{gameA}"
%format gameB = "\F{gameB}"
\todo{Need a good convention for |as| vs |AS|, etc.}
So far, we have only defined a syntax for the expression of games.  There is a natural valuation for this syntax in the
|StateT as Rnd| monad transformer, where |Rnd| is some monad with randomness support (e.g. |Rand StdGen| from
\texttt{MonadRandom}).  \todo{This feels like too little explanation, but more feels like too much.}  Given a game of
type |Game as A| it is thus possible to execute it and obtain some |a| of type |A| as the result. We will use this
interpretation in order to define two notions of indistinguishability between games.

We say that two games |g0| and |g1| of type |Game AS A| (for some |AS| and |A|) are \emph{result-indistinguishable}
iff for every initial adversary state and every |a| of type |A|, the probability of |g0| resulting in |a|
is equal to the probability of |g1| resulting in |a|.  We say that two games are \emph{(strictly) indistinguishable} iff
for every initial adversary state, every |a| of type |A|, and every |as| of type |AS|, the probability of the adversary
ending in state |as| with the game resulting in |a| is equal for |g0| and |g1|.

Returning to the previous example, an encryption scheme $\sigma$ is secure against eavesdropping iff |eav_game sigma
adv| is result-indistinguishable from |flipCoin| for every adversary |adv|.  However, it would be unreasonable to expect
|eav_game sigma adv| to be strictly indistinguishable from |flipCoin|, since |flipCoin| necessarily does not change the
adversary's state.  The property of strict indistinguishability is nevertheless useful, since substitution of strictly
indistinguishable terms produces strictly indistinguishable games, while substitution of merely result-indistinguishable
terms does not necessarily produce result-indistinguishable games.

\todo{I have the feeling this introduction is dragging on and on.}
We now have two results that are key to the kind of proofs we will be showing.  We assume |AS|, |A|, |B|, and |C| are fixed
types.

\begin{theorem}
    Given |g0 :: forall as dot Game as A|, |g1 :: forall as dot Game as B|, and |h : A -> B -> Game AS C|, the following
    games are indistinguishable:
    \begin{code}
    gameA = g0 >>= \ a -> g1 >>= \ b -> h a b
    gameB = g1 >>= \ b -> g0 >>= \ a -> h a b
    \end{code}
\end{theorem}
%}

\begin{theorem}
    Given |g :: Game AS A| and |h :: forall as dot Game as B|, |g >> h| is result-indistinguishable from |h|.
\end{theorem}

\section{Example: One-Time Pad}

Let us now put the above together to express that the One-Time XOR Pad encryption scheme is secure against
eavesdropping, but not secure if the adversary has access to the encryption function.

We can define the encryption scheme in Haskell as follows:
\begin{code}
    generateKeyOTP :: Int -> Game as BitVector
    generateKeyOTP = uniform

    encryptOTP :: BitVector -> BitVector -> Game as BitVector
    encryptOTP key msg = return (xor key msg)
\end{code}

Here, the |Int| taken by |generateKeyOTP| is the security parameter $n$.  We require that the two messages we receive
from the adversary be exactly $n$ bits long: otherwise, the adversary could choose $0^{n+1}$ and $1^{n+1}$ as his
messages, knowing that the last bit will not change.  Similarly, given messages of different lengths, the adversary
could use the length to find what message was used.\footnote{In the formalised version in Agda, this is achieved by
using a |BitVector| type that specifies the exact length of the strings.}

\subsection{Eavesdropper Attack}

We now regard the |eav_game| from before specialised for the OTP encryption scheme, and parametrised by the security
parameter |n|.  Our goal is to show that for any adversary |adv|, the following game is indistinguishable from a coin
flip:
\begin{code}
otp_game :: Int -> Adversary as pt ct -> Game as Bool
otp_game n adv = do
    k                <- generateKeyOTP n
    (m0 comma m1)    <- chooseMessages adv
    b                <- flipCoin
    m'               <- encryptOTP k (if b then m1 else m0)
    b'               <- chooseOutcome adv m'
    return (eq b b')
\end{code}

Note that we know that |generateKeyOTP| and |encryptOTP| do not access the adversary's state, and so the choice of |k| is
independent of the choices of |m0|, |m1|, and |b|.  We can thus rewrite the game as follows:
\begin{code}
otp_game1 :: Int -> EAV_Adversary as pt ct -> Game as Bool
otp_game1 n adv = do
    (m0 comma m1)  <- chooseMessages adv
    b              <- flipCoin
    m'             <- (if b  then  generateKeyOTP n >>= \ k -> encryptOTP k m0
                             else  generateKeyOTP n >>= \ k -> encryptOTP k m1)
    b'             <- chooseOutcome adv m'
    return (eq b b')
\end{code}

Inspecting the definitions of |generateKeyOTP| and |encryptOTP|, we see that the first generates a uniform distribution
and the second performs a XOR.  We can thus rewrite this game to be:
\begin{code}
otp_game2 :: Int -> EAV_Adversary as pt ct -> Game as Bool
otp_game2 n adv = do
    (m0 comma m1)  <- chooseMessages adv
    b              <- flipCoin
    m'             <- (if b  then  fmap (\ k -> (xor k m0)) (uniform n)
                             else  fmap (\ k -> (xor k m1)) (uniform n))
    b'             <- chooseOutcome adv m'
    return (eq b b')
\end{code}

The uniform distribution over bitstrings of length |n| is invariant under XOR with another bitstring of length |n|,
since the latter is a bijective mapping, so |fmap (\ k -> (xor k m0)) (uniform n)| can be simplified to |uniform n|.
This gives us the following game:
\begin{code}
otp_game3 :: Int -> EAV_Adversary as pt ct -> Game as Bool
otp_game3 n adv = do
    (m0 comma m1)  <- chooseMessages adv
    b              <- flipCoin
    m'             <- uniform n
    b'             <- chooseOutcome adv m'
    return (eq b b')
\end{code}

Since |m'| no longer depends on |b|, we can reorder the game to be:
\begin{code}
otp_game4 :: Int -> EAV_Adversary as pt ct -> Game as Bool
otp_game4 n adv = do
    (m0 comma m1)  <- chooseMessages adv
    m'             <- uniform n
    b'             <- chooseOutcome adv m'
    b              <- flipCoin
    return (eq b b')
\end{code}

In this game, |b| is generated once |b'| is fixed; thus |b == b'| is equivalent to either |b| or |not b|.  Since |fmap
not flipCoin| is indistinguishable from |flipCoin|, in both cases this is indistinguishable from |flipCoin|, as far as
the result is concerned.  By our assumption that the adversary reverts the state to the initial one, this computation is
thus as a whole indistinguishable from |flipCoin|.

\subsection{Chosen-Plaintext Attack}

By modifying the game slightly, we can consider the scenario where the adversary has access to the encryption function
used by the challenger.  This is known as the Chosen-Plaintext Attack.  In this case, the adversary receives not only an
encrypted message as the input to |chooseOutcome|, but also the encryption function itself.

%format CPA_Adversary = "\F{CPA\_Adversary}"
%format otp_cpa_game = "\F{otp\_cpa\_game}"
%format otp_cpa_adv_cm = "\F{otp\_cpa\_adv\_cm}"
%format otp_cpa_adv_co = "\F{otp\_cpa\_adv\_co}"

%format getAdvState = "\F{getAdvState}"
%format putAdvState = "\F{putAdvState}"

\begin{code}
data CPA_Adversary as pt ct  = CPA_Adversary
                             { chooseMessages  :: Game as (pt comma pt)
                             , chooseOutcome   :: ct
                                               -> (pt -> Game s ct)
                                               -> Game as Bool
                             }

otp_cpa_game :: Int -> CPA_Adversary as pt ct -> Game as Bool
otp_cpa_game n adv = do
    k              <- generateKeyOTP n
    (m0 comma m1)  <- chooseMessages adv
    b              <- flipCoin
    m'             <- encryptOTP k (if b then m1 else m0)
    b'             <- chooseOutcome adv m' (encryptOTP k)
    return (eq b b')
\end{code}

Since the |encrypt| function of OTP is at once its |decrypt| function, it is clear that the adversary can simply apply
it to |m'| and return the correct value.  We can express this in code as follows, with the |Int| parameter being the
security parameter used for the game:
\begin{code}
otp_cpa_adv_cm :: Int -> Game (BitVector comma BitVector) (BitVector comma BitVector)
otp_cpa_adv_cm n = do
    m0  <- uniform n
    m1  <- uniform n
    putAdvState (m0 comma m1)
    return (m0 comma m1)

otp_cpa_adv_co  :: BitVector
                -> (BitVector -> Game (BitVector comma BitVector) BitVector)
                -> Game (BitVector comma BitVector) Bool
otp_cpa_adv_co m' e = do
    (m0 comma m1) <- getAdvState
    putAdvState (undefined comma undefined)
    return (eq (e m1) m')
\end{code}

The |putAdvState (undefined comma undefined)| line is necessary to satisfy our guarantee that the initial adversary
state is equal to the final adversary state.  For the rest, the algorithm is straightforward.  A more interesting
question, however, is where the proof we provided for the Eavesdropper case breaks down.

The problem with that proof is that |k| is now used not only for the generation of |m'|, but is also passed (indirectly)
to |chooseOutcome|.  A certain relation holds between |m'| and |k|, and thus if we replace |encrypt k (if b then m0 else
m1)| with |uniform n| then we must also replace all later appearances of |k| with |(xor m' (if b then m0 else m1))| to
maintain this relationship.  Doing this, however, brings the proof no further, since the |chooseOutcome| call still
depends on |b|, and an essential step of the proof was making the adversary commit to a |b'| before |b| was chosen.

%}

\section{Formalised Proofs}

In the above, have used Haskell to precisely express the programs we were discussing, but reasoned about their
equivalence only at an informal level.  This is a reasonable approach when the programs in question are so simple, but
becomes increasingly error-prone as we move to more complicated algorithms, which require considerably more bookkeeping.
Since cryptographic algorithms are often used in safety-critical\todo{mission-critical? government?} contexts, it is
worth going the extra distance to verify their correctness formally in a proof-assistant.

We have chosen Agda as the language of formalisation, since it provides extensive support for dependent types, which
make it possible to express the notions we are working with in natural ways.  In particular, it allows us to use the
same language to express the games, challengers, adversaries, and properties of the above, all in the same language.

Our work in expressing games is strongly inspired by Peter Hancock's Interaction Structures.\todo{cite}  We will also
make use of Ulf Norell's \texttt{agda-prelude}\footnote{\url{https://github.com/UlfNorell/agda-prelude}} library.

