\chapter{Indexed Monads}

We have seen that certain properties, such as the number of oracle calls that an
adversary is allowed to make, would best be bounded on the level of the monad.
However, if we add these constraints as parameters of |CryptoExpr|, we can no
longer define the bind operation with the signature required for a monad.  We
can correct this issue by using an indexed monad.

\section{Definition}

The functions |S -> Set| form a category |SetS|, with the morphisms being
|S|-indexed families of morphisms.  This gives rise to the notion of a functor
on this category:
\begin{code}
_=>_ : (S -> Set) -> (S -> Set) -> Set
a => b = forall {s} -> a s -> b s

record IxFunctor {S : Set}(F : (S -> Set) -> (S -> Set)) : Set1 where
  field
    fmapi : (a => b) -> (F a => F b)
\end{code}

The natural transformations between these functors give rise to another category
\begin{code}
_~>_  :  ((S -> Set) -> (S -> Set))
      -> ((S -> Set) -> (S -> Set))
      -> Set1
F ~> G = forall {a} -> F a => G a
\end{code}

An indexed monad is a monoid in this category, that is:
\begin{code}
record IxMonad {S : Set}(F : (S -> Set) -> (S -> Set)) : Set1 where
  field
    overlap {{ixfunctorsuper}} : IxFunctor F
    returni : a => F a
    joini   : F (F a) => F a
\end{code}

As with normal monads, we typically find the bind operation of more practical
use than the join:
\begin{code}
  bindi : F a s -> (a => F b) -> F b s
\end{code}

Note that flipping the arguments we get |(a => F b) -> (F a => F b)|.

\section{Examples}

We can use the index to track how many oracle queries the adversary can make by
adding an index to the |CryptoExpr| type.  The resulting type becomes
\begin{code}
data CryptoExpr : (Nat -> Set) -> (Nat -> Set) where
  Return       : a k                                                 -> CryptoExpr a k
  Uniform      : (n : Nat)    -> (BitVec n      ->  CryptoExpr a k)  -> CryptoExpr a k
  GetAdvState  :              -> (AdvState      ->  CryptoExpr a k)  -> CryptoExpr a k
  SetAdvState  : AdvState     ->                    CryptoExpr a k   -> CryptoExpr a k
  InitOracle   : OracleState  ->                    CryptoExpr a k   -> CryptoExpr a k
  CallOracle   : OracleArg    -> (OracleResult  ->  CryptoExpr a k)  -> CryptoExpr a (suc k)
\end{code}

We can remark here that since |k| can only shrink, we can make a stronger
operator than |bindi|, namely one which only has to handle cases where the
number of allowed queries is less than or equal to the previous.  As per the
Intrinsically-Typed Interpreters paper, this should correspond to a strictening
of the functors that |CryptoExpr| accepts.  (I am still not quite sure how the
category structure gives rise to this.)

Another example is the indexed state monad: we can choose a universe and an
evaluation function and then provide a monad (in fact, monad transformer) that
stores a type and a value of that type.

\section{Reindexing Morphisms}

Sometimes, we want to speak about maps between indexed monads with different
index sets.  There are surprisingly many ways to do this, and it's probably
worth mentioning at least the main ones.
