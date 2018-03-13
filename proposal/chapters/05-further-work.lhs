\chapter{Research Plan}

We have now outlined the results we have obtained from our research so far.  We will conclude the proposal with a
demonstration of the formalised version of the example presented in the introduction, and with a discussion of the
issues that we have yet to resolve.

\section{One-Time Pad Revisited}

In the introduction, we showed an encryption scheme where the key was a random $n$-bit string |k| and the encryption
operation took the bitwise XOR of |k| and the message to be encrypted.  We showed that this scheme is secure against
eavesdropping, but not secure against a chosen-plaintext attack.  We will now outline how the first of these results can
be formalised in the system we have so far created.

Due to limitations of the implementation, the proof we present here does not allow the adversary to store any state.  We
will later discuss the consequences of this.

We can define the notions of an encryption scheme and adversary as follows, together with the game that will be played:
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

We can now define the OTP encryption scheme |OTP : Nat -> Scheme|\todo{Give technical details?} and construct a term
%{
%format OTPisINDEAV = "\F{OTP-is-IND-EAV}"
\begin{code}
OTPisINDEAV  : forall {n}(A : SimpleEavAdv (OTP n))
             -> coin ==D (VAL (simpleINDEAV (OTP n) A))
\end{code}
%}
where |==D| signifies indistinguishability\todo{This should come in an earlier chapter}: in other words, we can show
that for any value of the security parameter, the one time pad has perfect security.  The proof is, unfortunately,
rather long: it spans roughly 150 lines and contains many steps such as
\begin{code}
   lbracket  uniformexpr n  >>= \ k 
   ->        A2 k           >>= \ b'
   ->        coinexpr       >>= \ b
   ->        return (eq b b') rbracket
    ==D congbind  (uniformexpr n)
                  (  \ k   -> A2 k      >>=
                     \ b'  -> coinexpr  >>=
                     \ b   -> return (eq b b'))
                  (  \ k   -> coinexpr  >>=
                     \ b   -> A₂ k      >>=
                     \ b'  -> return (eq b b'))
                  (  \ k   -> interchangeinterpretation (A2 k) coinexpr
                               (\ b' b -> return (eq b b'))) ⟩
  (    uniformexpr n      >>= \ k
   ->  coinexpr           >>= \ b
   ->  A2 k               >>= \ b'
   ->  return (eq b b') )
\end{code}

This step argues that the game at the top is equivalent to the game at the bottom, since it is merely an interchange of
independent operations.  However, in order to express this, we must almost entirely duplicate each game!  Ideally, we
would like to condense this to only the essential part, namely that |A₂ k| and |coin-expr| should be interchanged in the
game.  We hope to be able to achieve this with a combination of reflection and proof search.

\subsection{Stateful Adversaries}

Since the above proof only holds for stateless adversaries, could it be that the result will fail once we introduce
adversary state?  We consider this unlikely, as the proof is expressed using the combinators that we have introduced in
this proposal.  We have shown on paper that these combinators preserve equivalence of games, but have not yet
constructed the corresponding proofs in Agda.  Once this is done, the proof could thus be generalised to stateful
adversaries without significant issue.

One shortcut we used that must be avoided for stateful adversaries is the separate elimination of the |A1| and |A2|
calls.  The essence of the proof is that once we have rewritten the program to be of the form
\begin{code}
  lbracket   A1         >>= \ m
  ->         cdots      >>= \ ct
  ->         A2 ct      >>= \ b'
  ->         coinexpr rbracket
\end{code}
we can eliminate all but the last expression.  When the adversary is stateless, we can do this by using irrelevance to
eliminate |A2 ct|, then the expression before it, and so on until |A1|.  However, if the adversary is stateful, |A1|
changes the state type to some |sigma| and |A2| changes it back to |top|.  Since we want the game as a whole (even when
rewritten) to have type |CryptoExpr top top Bool|, we must eliminate |A1| and |A2| at the same time.  We can do this by
using the monad laws to reassociate the game into

\begin{code}
  lbracket   (A1         >>= \ m
  ->         cdots       >>= \ ct
  ->         A2 ct)      >>= \ b'
  ->         coinexpr rbracket
\end{code}
where we can use irrelevance to eliminate all of the previous steps at once.

\subsection{CPA Example}

In the introduction, we showed that OTP is EAV-secure but not CPA-secure.  We have not been able to reproduce it in Agda
in its entirety, but the proof techniques we have at the moment are sufficient to demonstrate it.  We will now outline
how this can be done.  The definition of an encryption scheme remains unchanged.  The adversary and game can be defined
as follows:
\begin{code}
record SimpleCPAAdv (E : EncScheme) : Set1 where
  constructor simplecpaadv
  open EncScheme E
  field 
    A1  : CryptoExpr (PT * PT)
    A2  : (PT * PT)
        -> (PT -> CryptoExpr CT)
        -> CT
        -> CryptoExpr Bool

simpleINDCPA : (E : EncScheme)(A : SimpleCPAAdv E) -> CryptoExpr Bool 
simpleINDCPA E A 
  = keygen                               >>= \ k 
  -> A1                                  >>= \ m
  -> coinexpr                            >>= \ b
  -> enc k (if b then fst m else snd m)  >>= \ ct
  -> A2 m (enc k) ct                     >>= \ b' 
  -> return (eq b b') 
  where
    open EncScheme E
    open SimpleCPAAdv A
\end{code}
Here we still do not use adversary state, but pass the messages chosen by the advesrary when we ask it to identify the
plaintext that corresponds to the ciphertext.  

We can also express the adversary that has non-zero advantage in this game:
%{
%format gen = "\F{adv-gen}"
%format decide = "\F{adv-decide}"
%format adversary = "\F{adversary}"
%format replicatebv = "\F{replicate-bv}"
\begin{code}
gen : forall n -> CryptoExpr (BitVec n * BitVec n)
gen n = return (replicatebv n true , replicatebv n false) 
decide  : forall n
        -> (BitVec n * BitVec n)
        -> (BitVec n -> CryptoExpr (BitVec n))
        -> BitVec n
        -> CryptoExpr Bool
decide n (m0 , m1) o ct = fmap (\ ct' -> (eq ct ct')) (o m0)
adversary : forall n -> SimpleCPAAdv (OTP n)
adversary n = simplecpaadv (gen n) (decide n)
\end{code}
%}

We would like to show that for all $n > 0$\footnote{If $n = 0$ then the type of plaintext messages is a singleton; it is
thus indeed impossible to distinguish between any two messages, simply because they are necessarily the same message.}
that there is some |b : Bool| such that |sample coin b| (i.e. $\frac 1 2$) is unequal to |sample (VAL (simpleINDCPA
(OTP n) (adversary n))) b|.

We can rewrite |VAL (simpleINDCPA (OTP n) (adversary n))| usign already considered techniques, resulting in the
following game:
\begin{code}
    coinexpr >>= \ b -> return (eq b (eq tv (if b then tv else fv)))
\end{code}
where |tv| is the bit vector with all elements |true| and |fv| the bit vector with all elements |false|.

At this point, we need an additional lemma: that if |fv| and |tv| are distinct, then |eq fv (if b then fv else tv)| is
|b|.  This is provable by pattern matching on |b|, and gives us the game
\begin{code}
    coinexpr >>= \ b -> return (eq b b)
\end{code}

Since we can show that |forall b -> ((eq b b)) == true|, we can use irrelevant to reduce this to |return true|.  The
problem thus becomes showing that |coin| and |return true| are not indistinguishable.\todo{We need to mention this
is a required property of distributions earlier.}  It is a fundamental property of distributions that |coin| is
distinguishable from |return b| for any |b : Bool|, giving the desired result.

\section{Further Work}

Although the system developed so far can already be used to express non-trivial results like the OTP proof above,
considerable work must still be done in order to be able to prove more complex properties.  There are three points on
which we will need to focus in particular, namely sub-perfect security, adversaries with oracle access, and proof
automation.

\subsection{Security Levels}

In practice, many cryptographical algorithms lack perfect security but are nevertheless interesting and practically
useful.  We can express weaker notions of security by relaxing the requirement of indistinguishability or by requiring
that the result only hold for a particular class of adversaries.

In the examples so far, we said that a game was unwinnable if the advantage of every adversary was exactly zero.  We can
weaken this statement by only requiring that the advantage by bounded by some $\epsilon$ (possibly dependent on the
security parameter).  Unfortunately, while this change is simple at the level of games, proving results in this new
setting requires a weaker notion than strict indistinguishability.  Further research is needed to find what the
appropriate notion is.

The other way in which security can be relaxed is by only considering adversaries that satisfy particular properties;
typically, that the amount of computation of number of queries that the adversary does is bounded by a polynomial in the
security parameter.  Since we have chosen to avoid a deep embedding\todo{Discuss this earlier}, it is unlikely that we
will be able to bound the amount of computation, since we cannot inspect how much computation an Agda function performs.
However, with further research, we may be able to bound the number of oracle queries that the adversary performs.

\subsection{Oracles}

We have avoided the discussion of oracles up to this point, since their implementation in Agda is still an open
question.  However, since oracles play an essential role in the proofs that we will be formalising, we will show several
uses of them in this chapter.

Simply speaking, an oracle is a stateful function that the adversary gains access to.  The adversary may query the
oracle, but may not inspect its state.  Furthermore, many proofs rely on counting the number of times an oracle is
accessed, expressing the advantage in terms of this number to show that if the number of queries is fixed (or
polynomial) in the security parameter, then by increasing the security parameter we can make the adversary's advantage
neglegible.

When the oracle is stateless, there should be no difference between giving the adversary access to the oracle and
passing the oracle function directly to the adversary as a parameter; the latter is simply more convenient from the
perspective of writing proofs.  If we had chosen to use a deep embedding for computations, we could likely construct
functions for rewriting adversaries between the oracle-style and the function-passing-style directly.  However, this
would make games, adversaries, and proofs even more cumbersome to express, and would moreover require proving that the
adversary cannot take our example and inspect the implementation of the functions it is passed!

% OLD:

In the remainder of the time available, we intend to in any case achieve the following:
\begin{itemize}
    \item Express the ability for the adversary to maintain state.
    \item Express games where the adversary has access to a (stateful) oracle.
    \item Express a relationship between games that is weaker than strict equivalence (equivalence up to some
    $\epsilon$).
    \item Express concrete bounds on the complexity of adversaries (e.g. number of oracle queries).
    \item Prove the correctness of common proof steps, to enable reuse.
    \item Finalize the implementation of all of the above.
\end{itemize}

In addition, we would like to achieve the following if time permits:
\begin{itemize}
    \item Show that portions of proofs can be automated using proof search.
    \item Use reflection to automatically invoke the proof search.
    \item Express asymptotic bouds on the complexity of adversaries.
    \item Evaluate the significance of the |Repeat| combinator.
    \item (?) Present the results in some kind of nice abstract way.
\end{itemize}

\section{Timetable and Planning}

TODO: Write neat text.
\begin{itemize}
    \itemsep0em
    \item February-March: expressing games, expressing encryption schemes, expressing proof techniques
    \item April-May: proving stronger results, start writing thesis (prior knowledge)
    \item June: write thesis (my results), prove leftover postulates, express things like polynomial-time adversaries
    \item July: integrate last results into thesis, correct final errors.
\end{itemize}

