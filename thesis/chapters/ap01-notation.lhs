\chapter{Notation}
\label{chp:notation}

\todo[inline]{Introduction}

\section{Built-in Types}

\todo[inline]{Expand}
Since we are using Ulf Norell's
prelude\footnote{\url{http://github.com/UlfNorell/agda-prelude}}, there are a
number of types that are defined for us.  For example, |Nat|, bottom, top,
products, sums, function types.

\section{Value Definitions}

\todo[inline]{Expand}
In Agda, we can introduce a name by specifying its type and then giving its
definition.  Here are some examples:
\begin{code}
five : Nat
five = (plus 2 3)

square : Nat -> Nat
square x = (times x x)
\end{code}

\section{Type Definitions}

\todo[inline]{Expand}
Agda supports two ways of defining data types: |data| and |record| definition.

A |data| definition inductively defines a type by specifying all of the ways in
which it can be constructed.  For example, the following defines the type of
natural numbers:
\begin{code}
data Nat : Set where
  zero  : Nat
  suc   : Nat -> Nat
\end{code}

We call |zero| and |suc| \emph{constructors}.  Give such a definition, we can
define functions by induction on the constructors:
\begin{code}
(plus) : Nat -> Nat -> Nat
plus zero m = m
plus (suc n) m = suc ((plus n m))
\end{code}

\todo[inline]{Empty pattern matches}

\todo[inline]{record types}

\section{Equality}

\todo[inline]{Write}

\section{Monads}

\todo[inline]{Write}
