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
%format simpleeavadv = "\F{simple-eav-adv}"
%format simpleINDEAV = "\F{simple-IND-EAV}"
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
  -> A2 ct                               >>= \ b′ 
  -> return (nxor b b′) 
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
 % TODO: Fix formatting here
\begin{code}
   lbracket  uniformexpr n  >>= \ k 
   ->        A2 k           >>= \ b'
   ->        coinexpr       >>= \ b
   ->        return (nxor b b') rbracket
    ==D congbind  (uniformexpr n)
                  (  \ k   -> A2 k      >>=
                     \ b'  -> coinexpr  >>=
                     \ b   -> return (nxor b b'))
                  (  \ k   -> coinexpr  >>=
                     \ b   -> A₂ k      >>=
                     \ b'  -> return (nxor b b'))
                  (  \ k   -> interchange-interpretation (A2 k) coinexpr
                               (\ b' b -> return (nxor b b'))) ⟩
  (    uniformexpr n      >>= \ k
   ->  coinexpr           >>= \ b
   ->  A2 k               >>= \ b'
   ->  return (nxor b b') )
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

\section{Further Work}



\subsection{Security Levels}

We have mentioned that depending on the requirements of the situation, we may want consider a scheme secure if
the adversary's advantage is always zero, or if it is bounded by a constant, or if it is bounded by a function vanishing
asymptotically in some security parameter.  In the discussion of the above games, we omit discussion of this: each of
the games can have any of these three conditions imposed upon it externally.  In the asymptotic case, we assume that the
entire construction is parametrised by this parameter.  Simililarly, we can impose polynomiality constraints upon these
definitions.  In all cases, we express that these bounds are satisfied by saying that the advantage is negligible.

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

