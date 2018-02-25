\chapter{Introduction}
\label{chp:introduction}

The goal of the reseach proposed in this document is to create a library for reasoning about cryptographic algorithms,
in particular to show their security properties.  Such proofs are not new\footnote{TODO: cite something}, and there is a
commonly used game-based approach~\cite{gameexamples} to formulating them.  In addition, there exist frameworks
of these proofs in special-purpose languages\footnote{E.g. EasyCrypt, \url{www.easycrypt.info}} and Coq\cite{fcf}.  Our
contribution is to create a comparable framework for the Agda programming language.

In the remainder of this chapter, we will give an informal introduction to the kind of cryptographic proofs that we are
interested in, using encryption schemes as a running example.  The next two chapters are dedicated to showing the
portion of the system which we have so far been able to formalise in Agda.  In the fourth chapter, we will present more
advanced cryptographic proofs and properties, which our system does not yet support, as motivation for further
development. In the final chapter we will give a summary of our plans to tackle these problems.

\section{Encryption and Games}

A secure encryption scheme is a finite set $K$ of keys together with (non-determinstic) functions $e : K \times A \to B$
and $d : K \times B \to A$, where $A$ is the set of possible plaintext messages and $B$ the type of possible ciphertext
messages, satisfying the following properties:
\begin{enumerate}
    \itemsep0em
    \item For any $k \in K$ and $a \in A$, $d(k, e(k, a)) = a$,
    \item and for any (non-determinstic) function $f : B \to A$, the probability that $f(e(k, a)) = a$ is
    $\frac{1}{|A|}$, with $k$ sampled uniformly from $K$ and $a$ sampled uniformly from $A$.
\end{enumerate}

In the second condition, we require that the probability be $|A|^{-1}$ rather than 0, since no matter the encryption
function, $f$ may ignore its inputs and sample from $A$ uniformly.  By luck, this will coincide with $a$ with
probability $|A|^{-1}$.  The condition thus states that any function that does not depend on the key does no better at
decrypting the messages than simply picking a plaintext at random.

The first of these properties can be proven in a straightforward manner, since the structure of $d$ and $e$ is known.
The second, however, requires reasoning about an arbitrary function $f$, which is difficult and error-prone.  However,
note that if $(K, e, d)$ is an encryption scheme and $a_0, a_1 \in A$, then for every $f : B \to A$, the probability
that $f(e(k, a)) = a$ with $k$ chosen uniformly from $K$ and $a$ chosen uniformly from $\{a_0, a_1\}$ is $\frac 1 2$.
If this were not so, then $f$ could return a unifromly random $a \in A$ for inputs other than $e(k, a_0)$ and $e(k,
a_1)$ and choose better than random for inputs of that form.  On the other hand, if the adversary cannot distinguish
between the ciphertexts of any two particular messages, then it certainly cannot decode any ciphertext.

We thus reformulate the condition as follows: for any probability distribution $D$ on $A \times A$ and any function $f :
A \times A \times B \to \{0, 1\}$, the probability that $f(a_0, a_1, e(k, a_i)) = i$ with $a_0, a_1$ sampled from $D$,
$k$ sampled uniformly from $K$, and $i$ sampled uniformly from $\{0, 1\}$ is exactly $\frac 1 2$.

It seems that we have not much advanced towards our goal, since we must still argue about an arbitrary function $f$.
However, we can now use game-playing techniques \cite{gameplayingproofs} to reformulate this condition as a game, which
is then amenable to rewriting.  In order to make this transition more natural, we regard the problem as an interaction
between several agents.

Suppose that we have three parties, Alice, Bob, and Eve.  Alice and Bob have agreed on a key $k$ in advance, which Eve
does not know, and are sending each other messages encrypted with that key.  Suppose that Eve intercepts one such
message: what information can she gain based on this?

By the argument above, we may assume that the plaintext of the message was chosen from some set $\{m_0, m_1\}$ of
messages that Eve had chosen.  The full situation can then be seen as a game as follows:

\begin{enumerate}
    \itemsep0em
    \item Alice chooses a key $k$.
    \item Eve chooses two messages, $m_0$ and $m_1$, and gives them to Alice.
    \item Alice flips a coin and gets a result $b \in \{0, 1\}$.
    \item Alice encrypts $m_b$ and gives the result, $m'$, to Eve.
    \item Eve chooses $b' \in \{0, 1\}$ and gives it to Alice.
    \item If $b = b'$ then Eve wins, otherwise Eve loses.
\end{enumerate}

Note that Bob does not figure in this interaction, since his actions do not influence the information Eve has.  As far as
we are concerned, this is a two-player game between the encrypter, Alice, and the eavesdropper, Eve.  The encrypter is
typically called the challenger, while the eavesdropper is called the attacker or the adversary.

From a mathematical perspective, the adversary is the collection of all parameters over which we would like to
universally quantify the security of our scheme.  Concretely, by letting Eve (non-detriministically) choose two
messages, we allow her to specify a probability distribution over $A \times A$ and sample from it.  Similarly, by
choosing $b'$ based on $e(k, m_b)$, Eve implicitly specifies the function $f$.  We assume that Eve can remember her
previous actions, making it unnecessary to explicitly pass $m_0$ and $m_1$ in step 4.

We will from now on describe games from the point of view of the challenger, while treating the adversary as a black
box.  The above game thus becomes:
\begin{enumerate}
    \itemsep0em
    \item Generate a key $k$.
    \item Receive messages $m_0$ and $m_1$ from the adversary.
    \item Flip a coin to get $b \in \{0, 1\}$.
    \item Encrypt $m_b$; call the result $m'$.
    \item Give the adversary $m'$ and get $b'$ back.
    \item Return $b = b'$.
\end{enumerate}

This can, in turn, be regarded as a program in some imperative language, or a computation in some monad.  Computations
performed by the challenger are known, so they can be directly encoded in the program.  Computations performed by the
adversary are given as parameters to the program.  For the moment, we will use Haskell to represent these computations
and assume that there is a monad |Game| that provides some source of randomness and some way for the adversary to
store its state of type |as|.
\begin{code}
data EncScheme key pt ct  = EncScheme
                          { forall dot generateKey :: Game as key
                          , forall dot encrypt :: key -> pt -> Game as ct
                          }

data EAV_Adversary as pt ct  = EAV_Adversary
                             { chooseMessages :: Game as (pt, pt)
                             , chooseOutcome :: ct -> Game as Bool
                             }

EAV_game :: EncScheme key pt ct -> EAV_Adversary as pt ct -> Game as Bool
EAV_game enc adv = do
    k <- generateKey enc
    (m0, m1) <- chooseMessages adv
    b <- flipCoin
    m' <- encrypt enc k (if b then m1 else m0)
    b' <- chooseOutcome adv m'
    return (b == b')
\end{code}

We now have a precise description of the game involved, and we can say that a scheme |enc| is secure against
eavesdropping iff |EAV_game enc adv| is `very close' to |flipCoin| for every choice of |adv|; in our original terms, if
Eve's probability of winning the game is close to 50\%.  This may seem counterintuitive: if the scheme is secure,
shouldn't Eve consistently lose the game?  However, clearly, a random algorithm will win the game 50\% of the time by
pure luck, and so we cannot demand that an adversary do worse.  If Eve could reliably lose the game, this would actually
be a sign that the scheme is \emph{insecure}, since an adversary that performs the same computations as Eve and then
flips the result could reliably win it.

We will now give a more rigorous definition of the |Game| monad in order to formalise this notion of distance.

\section{The |Game| Monad}

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
