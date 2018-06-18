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

\section{Indexed Monad Morphisms}

There is a notion of a morphism between two monads on a category.  This is
great, since it gives some laws that functions like |evalCE| from chapter 3 must
follow.  However, in the indexed case things are a bit harder: suppose that our
indexed monads are indexed over different categories, what then?

It turns out there are in fact several choices of morphisms and each gives a
category (though we kind of need Kan extensions to do that nicely).

\section{The Atkey Construction}

The advantage of indexed monads is that we can restrict what kind of actions can
be performed.  However, at face value, the type of bind is very restrictive: we
must be able to proceed no matter what state we end up in.  This is often not
what we want, since we may know what state we will actually arrive at.

In order to encode this we make an indexed type which is inhabited in exactly
one state, namely the one we care about.  This is called the Atkey trick.
\begin{code}
data Atkey (A : Set) : S -> S -> Set where
  V : A -> Atkey A s s
\end{code}

In the state in which we will arrive, we get the result of the type we chose.
In every other state, the type of results is empty, and so there are no cases to
handle.

However, this is sometimes not quite powerful enough for our purposes.  We
sometimes don't know exactly what state we will end up in, but would know if we
got the value.  For example, in an interaction structure, we do not know the
state a command will take us to, but we discover it once we get the result.
This gives rise to a generalisation of the Atkey trick:
\begin{code}
data DepAtkey (A : Set)(f : A → S) : S -> Set where
  DepV : (a : A){s : S} -> (hip : s == f a) -> DepAtkey A f s
\end{code}

Now once we receive the value, we know what state we are in and do not have to
handle that value in any other states.

Interestingly, this can also be expressed as a Kan extension:
\begin{code}
KanAtkey : (A : Set)(f : A -> S) -> S -> Set
KanAtkey A f = Lan f (const A)
\end{code}

In words, this takes the left Kan extension of the |const A : A -> Set| functor
along |f : A -> S|, giving a functor |S -> Set|.

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

I think that indexed monads should be able to capture IND-CCA's requirement that
the adversary not decrypt the ciphertext it is given by the challenger.  This
would be an interesting illustration, since this seems to be tracked dynamically
otherwise.
