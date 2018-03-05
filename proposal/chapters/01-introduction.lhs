\chapter{Introduction}
\label{chp:introduction}

The goal of the reseach proposed in this document is to create a library for reasoning about cryptographic algorithms,
in particular to show their security properties.  Such proofs are not new\footnote{TODO: cite something}, and there is a
commonly used game-based approach~\cite{gameexamples} to formulating them.  In addition, there exist frameworks
of these proofs in special-purpose languages\footnote{E.g. EasyCrypt, \url{www.easycrypt.info}} and Coq\cite{fcf}.  Our
contribution is to create a comparable framework for the Agda programming language.

The problems we are looking at typically have the following structure: the situation is described as a series of
interactions between a \emph{challenger} and an \emph{adversary}.  Both parties have access to a source of randomness.
The computations performed by the challenger are known, while the adversary may perform any computations.  At the end of
this series of computations, the adversary must give some `answer' which determines whether it wins or loses.  The goal
of a proof is to bound the probability with which the adversary can win.

In the remainder of this chapter, we will give an informal introduction to the kind of cryptographic proofs that we are
interested in, using encryption schemes as a running example.  The next two chapters are dedicated to showing the
portion of the system which we have so far been able to formalise in Agda.  In the fourth chapter, we will present more
advanced cryptographic proofs and properties, which our system does not yet support, as motivation for further
development. In the final chapter we will give a summary of our plans to tackle these problems.

\section{Encryption Schemes}

An \emph{encryption scheme} is a tuple $\sigma = (K, M_p, M_c, e, d)$ where $K$ and $M_p$ are finite sets\footnote{The
assumption that $M_p$ is finite is not essential, but makes the development easier.}, $e : K \times M_p \to M_c$, $d : K
\times M_c \to M_p$ and for any $k \in K$ and $m \in M_p$, $d(k, e(k, m)) = m$.  We can regard $K$ as the set of keys,
$M_p$ and $M_c$ as the sets of plaintext and ciphertext messages, and $e$ and $d$ as the encryption and decryption
functions.  We allow $e$ and $d$ to be non-deterministic functions.

We say that an encryption scheme $\sigma$ is \emph{secure} iff for any (non-deterministic) function $f : M_c \to M_p$,
the probability that $f(e(k, m)) = m$ with $k$ sampled uniformly from $K$ and $m$ sampled uniformly from $M_p$ is
$\abs{A}^{-1}$.  In other words, any function $f$ that does not depend on the choice of key does no better a job of
decrypting ciphertext than simply selecting a plaintext at random would, which gives the correct plaintext with
probability $\abs{A}^{-1}$.

Showing that an encryption scheme is secure involves reasoning about an arbitrary function $f$, which can be difficult
and error-prone.  However, note that if $m_0, m_1 \in M_p$ with $m_0 \neq m_1$, then for every $f : M_c \to M_p$, the
probability that $f(e(k, m)) = m$ with $k$ chosen uniformly from $K$ and $m$ chosen uniformly from $\{m_0, m_1\}$ is
$\frac 1 2$.  If this were not so, then $f$ could return a uniformly random $m \in M_p$ for inputs other than
$e(k, m_0)$ and $e(k, m_1)$ and choose better than random for inputs of that form.  On the other hand, if the adversary
cannot distinguish between the ciphertexts of any two particular messages, then it certainly cannot decode any
ciphertext.

We thus reformulate the condition as follows: an encryption scheme $\sigma$ is \emph{secure} iff for any probability
distribution $D$ on $M_p \times M_p$ and any function $f : M_p \times M_p \times M_c \to \{0, 1\}$, the probability that
$f(m_0, m_1, e(k, m_b)) = b$ with $(m_0, m_1)$ sampled from $D$, $k$ sampled uniformly from $K$, and $b$ sampled
uniformly from $\{0, 1\}$ is exactly $\frac 1 2$.

It seems that we have not much advanced towards our goal, since we must still argue about an arbitrary function $f$.
However, by reformulating this problem as an interaction between a \emph{challenger} and an \emph{adversary} we can use
game-playing techniques~\cite{gameplayingproofs} to more easily reason about the problem.

\section{Games as Security Conditions}

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
    \item If $b = b'$ then the adversary wins, otherwise the adversary loses.
\end{enumerate}

An adversary that returns a random $b'$ independent of $c$ will win 50\% of his games.  This is the `worst' an adversary
can do: if an adversary could win, say, 40\% of their games, then by negating their choice of $b'$ they could win 60\%
of their games, and are thus evidence of the existence of a better-than-random algorithm.

If an adversary beats the game against encryption scheme $\sigma$ with probability $p$, we say that it has an
\emph{EAV-IND$_\sigma$ advantage} of $\abs{p - 0.5}$.  When the game is clear from context, we will simply call this the
\emph{advantage}.

Reformulating the security condition once again, we say that an encryption scheme $\sigma$ is \emph{strictly secure
against eavesdropping} if for any adversary |adv| the EAV-IND$_\sigma$ advantage of |adv| is zero.

\section{Games as Programs}

So far, we have relied on the reader's intuitive understanding of the notion of a non-deterministic function to define
the possible actions of the challenger and the adversary.  Our goal, however, is to reason about these security notions
in a proof assistant, which requires a more rigorous definition of each game.  We will now show how these games can be
defined in Haskell.  This differs somewhat from the representation we will use in Agda, but conveys the correct idea.

We regard the game as a computation in some |Game| monad, parametrised by the state used by the adversary and the result
of the game.  Computations performed by the challenger are known, so they can be directly encoded in the program.
Computations performed by the encryption scheme and adversary are given as parameters to the program.  We then have the
following code:
%{
%format :: = "::"
\begin{code}
data EncScheme key pt ct = EncScheme
  { forall as dot generateKey  ::               Game as key
  , forall as dot encrypt      :: key -> pt ->  Game as ct
  }

data EAV_Adversary as pt ct = EAV_Adversary
  { chooseMessages  ::        Game as (pt , pt)
  , chooseOutcome   :: ct ->  Game as Bool
  }

EAV_game :: EncScheme key pt ct -> EAV_Adversary as pt ct -> Game as Bool
EAV_game enc adv = do
    k <- generateKey enc
    (m0 , m1) <- chooseMessages adv
    b <- flipCoin
    m' <- encrypt enc k (if b then m1 else m0)
    b' <- chooseOutcome adv m'
    return (b == b')
\end{code}
%}

The adversary state |as| is not used directly in this code, but we assume the adversary can put and get values of type
|as| as a monadic action, similarly to the |State as| monad.  We can thus imagine that the adversary may store the two
messages prior to returning them from |chooseMessages|, and then later get them in |chooseOutcome| in order to compute
the outcome.  Of course, since the adversary may choose any type |as|, it may store any info it wishes to.  On the other
hand, since all actions of the challenger must be valid for any choice of |as|, we know by parametricity that the
challenger cannot inspect this state.

Both the challenger and the adversary have access to the |flipCoin : Game as Bool| operation, which allows them to
perform non-deterministic computations.  For convenience, we also assume that there is a |uniform : Int -> Game as
BitVec| that provides a given number of bits of randomness at once.

This gives us a formal description of the game, but does not yet let us quantify the adversary's advantage.  For this,
we introduce semantics for the monad and require that the 

CLEAN UP FROM THIS POINT

In the last section, we showed how games can be seen as terms in some |Game| monad.  This monad represented a
computation that may use some random bits, and in which the adversary may manipulate their state.  This computation can
be interpreted into a concrete value given an initial state and an (infinite) stream of random bits.

The adversary should be free to choose what type they wish to use for their state, while the challenger should be unable
to in any way access or modify this state.  We can achieve this by parametrising |Adversary| by its state type, while
requiring that our encryption work for any adversary state type.  The example above then becomes
\begin{code}
data EncScheme key pt ct  = EncScheme
                          { generateKey :: forall as. Game as key
                          , encrypt :: forall as. key -> pt -> Game as ct
                          }

data EAV_Adversary as pt ct  = EAV_Adversary
                             { chooseMessages :: Game as (pt, pt)
                             , chooseOutcome :: ct -> Game as Bool
                             }

EAV_game :: EncScheme key pt ct -> EAV_Adversary as pt ct -> Game as Bool
EAV_game enc adv = do
    ... -- unchanged
\end{code}

Since the challenger has no information about |as|, they cannot perform any operation on it; there is also no way for
|generateKey| to somehow store the state to later use it in |encrypt|.  This correctness-by-parametricity approach has a
downside in Haskell, namely that the challenger could use a nonterminating computation such as |fix id| as a new
Adversary state.  This is not a serious problem for our purposes, since Agda is a total language and thus does not have
this issue.

\subsection{Operations}

There are three classes of operations supported by the |Game| monad: operations involving randomness, which may
be performed by both challenger and adversary, operations manipulating the adversary's state, which may only be
performed by the adversary, and operations manipulating oracle state, which may only be performed by the challenger.
Since we are not yet concerned with oracles, we will only cover the first two categories.

The fundamental operation involving randomness is the flipping of a fair coin.  From this we can build up random
bitstrings of any length.  The resulting operations provided are thus:
\begin{code}
fairCoin :: Game as Bool
uniform :: Int -> Game as BitVector
\end{code}

We have so far not provided any way of generating uniform distributions over sets with a size other than a power of two,
as this does not seem to be a common requirement in the domain of cryptography.  Furthermore, not supporting this allows
for an easier interpretation, since the number of random bits necessary per operation is fixed.

In addition to the above, the FCF provides a |repeat| operation which repeats some non-deterministic computation until a
predicate holds on the result.  More research is needed to see whether this is truly necessary for our purposes.  This
would, in particular, allow us to recover uniform distributions over arbitrary finite sets.

The adversary is given access to a state, which acts much like the state of a state monad.  There are corresponding
operations:
\begin{code}
getAdvState :: Game as as
putAdvState :: as -> Game as ()
\end{code}

\subsection{Interpretation}

Now that we have a set of operations, we need to specify their semantics.  We do this by specifying an interpretation of
this monad in a state monad that maintains the adversary state and the random bits.  Since |uniform| can be defined in
terms of |fairCoin|, we only need to provide interpretations forthe |fairCoin|, |getAdvState|, and |putAdvState|
operations.  In other words, we have the following type, together with three operations on it, and an interpertation
function:
\begin{code}
    data Interp as a = Interp (as -> Stream Bool -> (as, Stream Bool, a))
    fairCoin' :: Interp as Bool
    fairCoin' as (Cons r rs) = (as, rs, r)
    getAdvState' :: Interp as as
    getAdvState' as rs = (as, rs, as)
    putAdvState' :: as -> Interp as ()
    putAdvState' rs as' as = (as', rs, ())

    interpret :: Game as a -> Interp as a
\end{code}

We require that |interpret| send |fairCoin|, |getAdvState|, and (for every |as'|) |putAdvState as'| to |fairCoin'|,
|getAdvState'|, and |putAdvState' as'| respectively, in the sense that the resulting functions are equal on all inputs.

In general, we do not want to require this kind of strict equality for interpretations.  For example, the following two
games should be considered equivalent, even though their interpretations are not elementwise equal:
\begin{code}
game1 :: Game () (Bool, Bool)
game1 = do
    x <- flipCoin
    y <- flipCoin
    return (x, y)

game2 :: Game () (Bool, Bool)
game2 = do
    y <- flipCoin
    x <- flipCoin
    return (x, y)
\end{code}

The condition we impose is as follows: games $A$ and $B$ have the same interpretation if for any choice of initial
adversary state |as|, |interpret A as| and |interpret B as| give rise to the same distributions when applied to the
uniform distribution over streams of bits.

Note that |flipCoin >> flipCoin| is equivalent to |flipCoin| in this sense, even though one uses more random bits than
the other: both give rise to distributions over triples |(rs, as, a)|, where |rs|, |as|, and |a| are independent.  The
distributions on |as| and |a| clearly agree.  The distributions on |rs| also agree, since any tail of a uniformly random
bitstring will itself be uniformly random.  In fact, we shall prove that |rs| is \emph{always} independent of |(as, a)|
and always uniformly distributed, so it suffices to look at the distributions of |(as, a)|.

The choice to keep adversary state visible allows for more precise intermediate reasoning, but comes at the cost of a
small complication when considering the program as a whole: an adversary that modifies state and then guesses at random
can be distinguished from an adversary that simply guesses at random, while the two are equivalent from the point of
view of whether they can break our encryption scheme.  We thus require that when considering the game as a whole, the
adversary resets its state to the initial one as part of the last step.

We can use this to quantify the distance between two games: since they are probability distributions, we can consider
any metric on the space of probability distributions as the distance between the two.  In practice, we are typically
interested in an upper bound on the difference in the outcomes.  Since both the output type and the adversary's state
type are typically finite, we can fix an adversary's initial state and then take the sum over the absolute differences
in the probabilities of outcomes.

We refer to this distance as the adversary's \emph{advantage}.  If no adversary is specified, we mean the maximum
advantage any adversary can have for the game in question.

\section{Security Constraints}

We now have a notion of games and a notion of closeness of games, but this does not yet give us a condition for what we
consider `very close'.

A very strong notion of closeness is indistinguishability, as desribed above; the requirement that for every initial
adversary state, the distributions over the final adversary states and outputs are identical.  This is a lofty goal to
aspire to, but is often unreachable in practice due to the the adversary being able to guess with odds that are
slightly better than random chance.  If we can nevertheless bound these odds, we can still quantify the security of the
scheme in question, despite this security not being perfect.

We therefore also use a weaker notion of closeness, namely an upper bound on the distance between the resulting
distributions.  We say that two distributions are $\epsilon$-indistinguishable if their distance is at most $\epsilon$.
We say that two games are $\epsilon$-indistinguishable if the best advantage an adversary can have is at most
$\epsilon$.  This is known as concrete security, since we give a concrete bound on the chance with which the adversary
can break the scheme.

The above has the downside that in the case of many schemes, adversaries can be constructed that will win the game with
arbitrarily high probability.  Nevertheless, these schemes are still secure if we take an asymptotic perspective: by
letting the scheme depend on some security parameter $n$ and requiring that every adversary's advantage be bounded by a
vanishing function of $n$, we can be sure that even though any concrete instance of the scheme can be broken by some
adversary, that adversary cannot break harder versions effectively.  This is typically known as asymptotic security.

Although asymptotic security is a very useful notion, it relies on the adversary being uniform in the choice of $n$,
which is hard to guarantee in Agda.  Additionally, it may involve restricting the number of operations (of whatever
kind) that the adversary can make to some polynomial in $n$.  Expressing these properties in Agda is non-trivial, and
will be a major research point of this thesis.

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

Here, the |Int| taken by |generateKey| is the security parameter $n$.  We require that the two messages we receive from
the adversary be exactly $n$ bits long: otherwise, the adversary could choose $0^{n+1}$ and $1^{n+1}$ as his messages,
knowing that the last bit will not change.  Similarly, given messages of different lengths, the adversary could use the
length to find what message was used.\footnote{In the formalised version in Agda, this is achieved by using a
|BitVector| type that specifies the exact length of the strings.}

\subsection{Eavesdropper Attack}

We now regard the |EAV_game| from before specialised for the OTP encryption scheme, and parametrised by the security
parameter |n|.  Our goal is to show that for any adversary |adv|, the following game is indistinguishable from a coin
flip:
\begin{code}
otp_game :: Int -> Adversary as pt ct -> Game as Bool
otp_game n adv = do
    k <- generateKeyOTP n
    (m0, m1) <- chooseMessages adv
    b <- flipCoin
    m' <- encryptOTP k (if b then m1 else m0)
    b' <- chooseOutcome adv m'
    return (b == b')
\end{code}

Note that we know that |genearteKeyOTP| and |encryptOTP| do not access the adversary's state, and so the choice of |k| is
independent of the choices of |m0|, |m1|, and |b|.  We can thus rewrite the game as follows:
\begin{code}
otp_game1 :: Int -> Adversary as pt ct -> Game as Bool
otp_game1 n adv = do
    (m0, m1) <- chooseMessages adv
    b <- flipCoin
    m' <- (if b then generateKeyOTP n >>= \k -> encryptOTP k m0
                else generateKeyOTP n >>= \k -> encryptOTP k m1)
    b' <- chooseOutcome adv m'
    return (b == b')
\end{code}

Inspecting the definitions of |generateKeyOTP| and |encryptOTP|, we see that the first generates a uniform distribution
and the second performs a XOR.  We can thus rewrite this game to be:
\begin{code}
otp_game2 :: Int -> Adversary as pt ct -> Game as Bool
otp_game2 n adv = do
    (m0, m1) <- chooseMessages adv
    b <- flipCoin
    m' <- (if b then fmap (\k -> xor k m0) (uniform n)
                else fmap (\k -> xor k m1) (uniform n))
    b' <- chooseOutcome adv m'
    return (b == b')
\end{code}

The uniform distribution over bitstrings of length |n| is invariant under XOR with another bitstring of length |n|,
since the latter is a bijective mapping, so |fmap (\k -> xor k m0) (uniform n)| can be simplified to |uniform n|.  This
gives us the following game:
\begin{code}
otp_game3 :: Int -> Adversary as pt ct -> Game as Bool
otp_game3 n adv = do
    (m0, m1) <- chooseMessages adv
    b <- flipCoin
    m' <- uniform n
    b' <- chooseOutcome adv m'
    return (b == b')
\end{code}

Since |m'| no longer depends on |b|, we can reorder the game to be:
\begin{code}
otp_game4 :: Int -> Adversary as pt ct -> Game as Bool
otp_game4 n adv = do
    (m0, m1) <- chooseMessages adv
    m' <- uniform n
    b' <- chooseOutcome adv m'
    b <- flipCoin
    return (b == b')
\end{code}

In this game, |b| is generated once |b'| is fixed; thus |b == b'| is either |b| or |not b|.  Since |fmap not flipCoin|
is indistinguishable from |flipCoin|, in both cases this is indistinguishable from |flipCoin| from the point of view of
the result.  By our assumption that the adversary reverts the state to the initial one, this computation is thus as a
whole indistinguishable from |flipCoin|.

\subsection{Chosen-Plaintext Attack}

By modifying the game slightly, we can consider the scenario where the adversary has access to the encryption function
used by the challenger.  This is known as the Chosen-Plaintext Attack.  In this case, the adversary receives not only an
encrypted message as the input to |chooseOutcome|, but also the encryption function itself.
\begin{code}
data CPA_Adversary as pt ct  = CPA_Adversary
                             { chooseMessages  :: Game as (pt, pt)
                             , chooseOutcome   :: ct
                                               -> (pt -> Game s ct)
                                               -> Game as Bool
                             }

otp_cpa_game :: Int -> CPA_Adversary as pt ct -> Game as Bool
otp_cpa_game n adv = do
    k <- generateKeyOTP n
    (m0, m1) <- chooseMessages adv
    b <- flipCoin
    m' <- encryptOTP k (if b then m1 else m0)
    b' <- chooseOutcome adv m' (encryptOTP k)
    return (b == b')
\end{code}

Since the |encrypt| function of OTP is at once its |decrypt| function, it is clear that the adversary can simply apply
it to |m'| and return the correct value.  We can express this in code as follows, with the |Int| parameter being the
security parameter used for the game:
\begin{code}
    otp_cpa_adv_cm :: Int -> Game (BitVector, BitVector) (BitVector, BitVector)
    otp_cpa_adv_cm n = do
        m0 <- uniform n
        m1 <- uniform n
        putAdvState (m0, m1)
        return (m0, m1)

    otp_cpa_adv_co :: BitVector
                   -> (BitVector -> Game (BitVector, BitVector) BitVector)
                   -> Game (BitVector, BitVector) Bool
    otp_cpa_adv_co m' enc = do
        (m0, m1) <- getAdvState
        putAdvState (empty, empty)
        return (enc m1 == m')
\end{code}

The |putAdvState (empty, empty)| line is necessary to satisfy our guarantee that the initial adversary state is equal to
the final adversary state.  For the rest, the algorithm is straightforward.  A more interesting question, however, is
where the proof we provided for the Eavesdropper case breaks down.

The problem with that proof is that |k| is now used not only for the generation of |m'|, but is also passed (indirectly)
to |chooseOutcome|.  A certain relation holds between |m'| and |k|, and thus if we replace |encrypt k (if b then m0 else
m1)| with |uniform n| then we must also replace all later appearances of |k| with |xor m' (if b then m0 else m1)| to
maintain this relationship.  Doing this, however, brings the proof no further, since the |chooseOutcome| call still
depends on |b|, and an essential step of the proof was making the adversary commit to a |b'| before |b| was chosen.

\section{Formalised Proofs}

The proofs in the previous section rely heavily on arguments about the independence of certain random values, as well as
on some conventions established for the adversary that cannot be expressed in the programming language the games
themselves are written in.  This is an unsatisfactory state of affairs, since verifying the correctness of these
arguments involves considerable work.  The situation only becomes worse when the challenger is also given the
opportunity to store state and some margin of error is permitted between games.

In order to remedify this, we will formalise both the games and the proofs about them in Agda.  This allows us to
enforce the restrictions we lay upon the challenger and adversary on the type level, and build up proofs using
known-good combinators.

A significant downside to this approach is that the proofs are often very verbose.  One of the goals of this thesis is
to look into how such work can be automated using proof search techinques and reflection.

\section{Existing Work}

TODO: Move this to the chapter where it is relevant.
A significant portion of the work shall be dedicated to the representation of probability distributions in a
dependently-typed programming language.  The implementations are based on \cite{stochasticlambdacalculus}, amongst
others.
