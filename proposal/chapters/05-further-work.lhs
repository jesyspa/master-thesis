\chapter{Research Plan}

In this proposal, we have outlined the research already done and the understanding we have achieved so far.  No less
significant are the technical results we have so far attained: at the moment of writing, the entirety of the
introduction has been formalised in Agda, with the exception of a lemma regarding invariance under bind, and the
counterexample to the security of the One-Time Pad encryption scheme with respect to a chosen-plaintext attack 
Additionally, the presentation we currently have has no support for adversary state.

Nevertheless, we can define an encryption scheme, an adversary, and a game as follows,
%format encscheme = "\F{enc-scheme}"
%format nxor a b  = "{" a "}\mathbin{\F{$\otimes$}}{" b "}"
\begin{code}
record EncScheme : Set1 where
  constructor encscheme
  field
    Key PT CT : Set
    
    keygen : CryptoExpr Key
    enc : Key → PT → CryptoExpr CT

record SimpleEavAdv (E : EncScheme) : Set₁ where
  constructor simple-eav-adv
  open EncScheme E
  field 
    A₁ : CryptoExpr (PT × PT)
    A₂ : CT → CryptoExpr Bool

simple-IND-EAV : (E : EncScheme)(A : SimpleEavAdv E) → CryptoExpr Bool 
simple-IND-EAV E A 
  =  keygen                              >>= \ k 
  -> A₁                                  >>= \ m
  -> coin-expr                           >>= \ b
  -> enc k (if b then fst m else snd m)  >>= \ ct
  -> A₂ ct                               >>= \ b′ 
  -> return (nxor b b′) 
  where
    open EncScheme E
    open SimpleEavAdv A
\end{code}

We can now define the OTP encryption scheme |OTP : Nat -> Scheme| and construct a term
\begin{code}
OTP-is-IND-EAV : ∀{n}(A : SimpleEavAdv (OTP n))
               → coin ≡D ⟦ simple-IND-EAV (OTP n) A ⟧
\end{code}
where |≡D| signifies indistinguishability: in other words, we can show that for any value of the security parameter,
the one time pad has perfect security.  The proof is, unfortunately, rather long: it spans roughly 150 lines and
contains many steps such as
\begin{code}
  ⟦( uniform-expr n  >>= λ k 
   → A₂ k            >>= λ b′
   → coin-expr       >>= λ b
   → return (nxor b b′) )⟧
    ≡D⟨ cong->>=  (uniform-expr n)
                  (  λ k   → A₂ k >>=
                     λ b′  → coin-expr >>=
                     λ b   → return (nxor b b′))
                  (  λ k   → coin-expr >>=
                     λ b   → A₂ k >>=
                     λ b′  → return (nxor b b′))
                  (  λ k   → interchange-interpretation (A₂ k) coin-expr
                               (λ b′ b → return (nxor b b′))) ⟩
  ⟦( uniform-expr n    >>= λ k
   → coin-expr         >>= λ b
   → A₂ k              >>= λ b′
   → return (nxor b b′) )⟧
\end{code}

This step argues that the game at the top is equivalent to the game at the bottom, since it is merely an interchange of
independent operations.  However, in order to express this, we must almost entirely duplicate each game!  Ideally, we
would like to condense this to only the essential part, namely that |A₂ k| and |coin-expr| should be interchanged in the
game.  We hope to be able to achieve this with a combination of reflection and proof search.

\section{Further Work}

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

