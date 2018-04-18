\section{Research Plan}
\label{sec:plan}

We have now outlined the results we have obtained from our research so far.  We will conclude the proposal with a
demonstration of the formalised version of the example presented in the introduction, and with a discussion of the
issues that we have yet to resolve.

\subsection{One-Time Pad Revisited}

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
   lbracket  uniformexpr n      >>= \ k
   ->        coinexpr           >>= \ b
   ->        A2 k               >>= \ b'
   ->        return (eq b b') rbracket
\end{code}

This step argues that the game at the top is equivalent to the game at the bottom, since it is merely an interchange of
independent operations.  However, in order to express this, we must almost entirely duplicate each game!  Ideally, we
would like to condense this to only the essential part, namely that |A₂ k| and |coinexpr| should be interchanged in the
game.  We hope to be able to achieve this with a combination of reflection and proof search.

\subsubsection{Stateful Adversaries}

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

\subsubsection{CPA Example}

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

\subsection{Further Work}

Although the system developed so far can already be used to express non-trivial results like the OTP proof above,
considerable work must still be done in order to be able to prove more complex properties.  There are three points on
which we will need to focus in particular, namely sub-perfect security, adversaries with oracle access, and proof
automation.

\subsubsection{Security Levels}

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

\subsubsection{Oracles}

As seen in chapter~\ref{chp:games}\todo{Do this}, oracles allow for the introduction of additional actors into our game
between challenger and adversary.  The challenger sets up a number of oracles, which the adversary can then query for
advice.  A simple example is an encryption oracle, which is given the key by the challenger and applies the encryption
function to strings that the adversary passes to it.

The above description opens up a very wide design space, where we hope to strike a balance between power and simplicity.
In the simplest case, an oracle can be regarded as a stateful function that the adversary can invoke, but whose state he
cannot access.  However, we may eventually want to provide multiple ways to query the same state, or to change the type
of the state in response to a query.  With sufficient generality, we could regard the adversary as a special case of an
oracle and thereby allow for multiple adversaries.  Such features, unfortunately, come with a cost both in
implementation time and often in the complexity of the resulting game descriptions.

Additionally, regardless of the specifics, oracles present some practical challenges.  Oracles may have state that the
adversary may not access.  We hope to be able to achieve this effect with parametricity, but this is typically not
provable within Agda and must thus be assumed.

Furthermore, many proofs rely on the adversary performing some fixed number of non-repeating queries to an oracle, often
before any other computation is performed.  Due to the monadic structure of our code, it is not even obvious that the
number of queries an adversary performs must be bounded, and there is no easy way to restructure the code of the
adversary.  These problems might be possible to address by modifying the adversary (for example, tracking adversary
queries and giving the previous response if the request has already been made previously), but it may also be necessary
to in some cases prove some claims externally (e.g. that adversaries can be rewritten in a given form) and then
postulate their formulations in Agda.

\subsubsection{Proof Automation}

As can be seen from the OTP example, expressing even simple proofs in the framework we have is too verbose to be of
practical use.  For a large part, this is due to every step having to express not only what changes, but also the full
context of the change.  In particular, significant duplication is caused by the |congbind| rule that allows us to
conclude |x >>= f| is indistinguishable from |x >>= g| if |f a| and |g a| are indistinguishable for all |a|: if |f| and
|g| are lambda terms then Agda cannot autodeduce them.  The entire right-hand side of each |>>=| to the left of the
changed term must be written out, giving a quadratic explosion in proof sizes.

One approach to reducing this problem is to not employ lambda terms when describing games.  This would allow us to
leverage the implicit argument feature of Agda for some of this work, but would require step-by-step descriptions of the
games to be written out separately.  The definition of each game would also be broken up, making it harder to regard
them in their entirety.

A more hopeful approach is to use reflection so that given an equality and a game, we can quote the game, inspect the
structure, and find where in the body we can perform a substitution using that equality.  We can then generate a proof
term based on this quoted representation, that can be unquoted to give an equality between games.

This approach can be split into two sections: obtaining a quoted representation of the game, and finding where in that
representation we can apply a given equality.  The first problem relies heavily on the implementation of reflection in
Agda, while the second is independent, requiring only a representation of quoted terms.  Both are viable additions to
the project, though we regard the latter as of more theoretical interest.

\subsubsection{Practical Examples}

In addition to the general developments described above, we also consider it important to prove the usefulness of this
system by formalising a number of existing proofs where it is possible, and identify the problems where it is not.

