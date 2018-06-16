\chapter{Rationals in Agda}

Throughout the thesis we assume that we have a type of rationals that satisfies
the properties we are interested in.  Is this choice significant?

\section{Necessary Properties}

Is there some clear list of which properties we truly need?  Would using the
reals work?  Would using floating point numbers work?

\section{The |Repeat| Combinator}

Existing libraries provide a |Repeat| combinator that allows you to retry a
computation until you get a result satisfying some predicate.  In Agda, this
could be modelled by a |CryptoExpr A| constructor
\begin{code}
Repeat  : (P : A -> Bool)(a : A) -> P a
        -> (ce : CryptoExpr A)
        -> Stateless ce
        -> (A -> CryptoExpr B)
        -> CryptoExpr B
\end{code}

This requires a finiteness assumption on |A|, forces you to have arbitrary
(non-zero) inverses in your probability type, and (I think) can be derived from
the latter, though probably not very easily.  (Basically, \emph{any} finite
distribution should be modellable anyway, so this does not add to the power of
the system, only to the expressivity.)
