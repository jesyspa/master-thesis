\chapter{Notation}
\label{chp:notation}

For the reader's convenience, we include an overview of the Agda features that
we use in this text.  This is by no means a comprehensive introduction to Agda,
nor do we include all features used in the accompanying code.  Our purpose is
primarily to make the text accessible to readers with a purely mathematical
background.

A more thorough overview can be found at
\url{https://agda.readthedocs.io/en/v2.5.4.1/}.

\section{Built-in Types}

Agda can be regarded as an implementation of the dependently typed
$\lambda$-calculus $\lambda\Pi$, corresponding to the internal language of locally
(bi)Cartesian closed categories.  In particular, finite product and and
coproduct types exist, as do function types, dependent function types, and
dependent product types.  The notation for these types is as follows:
\begin{itemize}
    \item The empty type is denoted |bot|.
    \item The unit type is denoted |top| and has a single element |tt : top|.
    \item The product of types |A| and |B| is denoted |A * B|.  Elements of this
    product are pairs |a , b| with |a : A| and |b : B|.
    \item The coproduct of types |A| and |B| is denoted |A + B|.  Elements of
    this coproduct are of the form |left a| with |a : A| or |right b| with |b :
    B|.
    \item The type of functions from |A| to |B| is denoted |A -> B|.  We shall
    give several examples of function definitions in
    \autoref{sec:notation-values}.  Functions are associated to the right, so |A
    -> B -> C| denotes |A -> (B -> C)|.
    \item The type of dependent functions that take an |a : A| and return a |B
    a| is denoted |(a : A) -> B|.  They are defined in the same way as
    non-dependent functions.
    \item The type of dependent pairs that contain an |a : A| in the first
    component and a |B a| in the second are denoted |Sigma A B|.
\end{itemize}

Additionally, Agda has an $\omega$-indexed hierarchy of universes: all basic
types are of type |Set|, which itself is of type |Set1|, and so on.  We also
assume that the types |Nat| of natural numbers, |Bool| of Booleans, and |Q| of
rational numbers are already available, together with the usual arithmetic and
comparison operations on them.

Finally, equality in Agda is expressed by means of an equality type |a == b|.
We will discuss this type in \autoref{sec:notation-equality}.

\section{Expressions}

Since Agda is based on the $\lambda$-calculus, the two most important kinds of
expressions it provides are uses of variables and function application.  The
first is what it would appear.  The second is denoted by juxtaposition, so |a b|
denotes the application of |a| to |b|.  Function application associates to the
left, so |a b c| denotes |(a b) c|.

Since operations such as addition are better written in infix form, Agda allows
definitions of names to choose a different syntax for their use.  This is done
by denoting the locations of the arguments by underscores.  We will see this
usage in the definition of |_+_| below, which defines addition as an infix
operator.  Another common usage is for the if-then-else construction:
\begin{code}
if_then_else_ : Bool -> A -> A -> A
if true   then e1 else e2 = e1
if false  then e1 else e2 = e2
\end{code}

Most syntax we use will be based on mathematical notation, and so will be
familiar to the reader.  One important exception is the |dollar| operator, which
is another way of denoting function application.  The expression |a dollar b|
simply means |(a) (b)|, but |dollar| has extremely low precedence, making it
suitable for writing terms such as |square dollar 2 + 1|, which evaluates to
|9|, rather |5|, as it would if we wrote |square 2 + 1|.

\section{Value Definitions}
\label{sec:notation-values}

In order to introduce a name in Agda, we specify its type and then give its
definition.  The syntax is as follows, with the first line giving the type, and
the second giving the definition.  A definition of the form |f x y = ldots|
defines a function |f| that takes parameters |x| and |y|.
\begin{code}
five : Nat
five = (plus 2 3)

square : Nat -> Nat
square x = (times x x)
\end{code}

In some cases, Agda can deduce the type of a name without it being explicitly
specified.  We will avoid using this for the sake of clarity.

Functions can also be defined with the use of lambda expressions.  The following
is equivalent to the definition of |square| above:
\begin{code}
square : Nat -> Nat
square = \ x -> (times x x)
\end{code}

\section{Type Definitions}

Agda supports two ways of defining new data types: |data| and |record|
definition.

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
_+_ : Nat -> Nat -> Nat
plus zero m = m
plus (suc n) m = suc ((plus n m))
\end{code}

Agda allows recursive definitions like the above, as long as it can prove that
the recursion is well-founded.  If the set of possible cases is empty, we can
replace the argument by |()| and omit the body, such as in the following
example:
\begin{code}
absurd : bot -> A
absurd ()
\end{code}

In order to do pattern-matching in lambda expressions, the body of the lambda
must be enclosed in curly braces.  We can, for example, define:
\begin{code}
pred : Nat -> Nat
pred = \ { (suc k) -> k ; zero -> zero }
\end{code}

The other way of defining a new data type is a |record| definition, which
defines a type by the fields it must provide.  For example, the following
defines the type of monoids over a type |A|:\footnote{Technically, a proper
definition would include the monoid laws, but these are typically omitted.}
%format Monoid = "\D{Monoid}"
%format operation = "\RF{op}"
%format identity = "\RF{e}"
\begin{code}
record Monoid (A : Set) : Set where
  field
    operation     : A -> A -> A
    identity      : A
\end{code}

We can define the addition monoid on the natural numbers as follows:
\begin{code}
Addition : Monoid Nat
op  Addition n m = n + m
e   Addition = 0
\end{code}

As a final note, we remark that Agda allows for implicit arguments in
definitions of functions and types.  These are placed within curly braces and do
not need to be specified when the corresponding name is used, as long as Agda
can deduce the value from other arguments.  For example, the identity function
is written as follows:
\begin{code}
id : (FORALL A) -> A -> A
id x = x
\end{code}

Since in a usage such as |id 5|, Agda knows that |A| must be |Nat| since that is
the type of |5|, we can omit the argument.  In this text we will generally omit
implicit arguments entirely, trusting the user to replace them; this allows us
to focus on the substance of the matter.

\section{Equality}
\label{sec:notation-equality}

In Agda, we can express equality of terms on the type level using the |==| type.
An element of type |a == b| is a proof that |a| and |b| are equal.  If that is
the case, there is a single constructor |refl : a == a|; otherwise, the type is
empty.  The Agda type system is aware of this, so pattern matching on |refl|
simplifies type goals.  For example, the following expresses the symmetry of
equality:
\begin{code}
sym : forall {a b} ->  a == b -> b == a
sym pf = ?
\end{code}

We call |?| a `hole', and use it to denote a piece of the program we have not
yet written.  Here, the type of the hole is |b == a|.  However, if we pattern
match on |pf|, then this type changes:
\begin{code}
sym : forall {a b} -> a == b -> b == a
sym refl = ?
\end{code}

Here, the type of |?| is |a == a|, since we know that |a| and |b| are equal, and
may thus replace |b| by |a| in the goal.  We can thus complete the definition:
\begin{code}
sym : forall {a b} -> a == b -> b == a
sym refl = refl
\end{code}

This is how equality is handled in proofs.  Equality of values at runtime is
handled separately: essentially, when we ask whether two natural numbers |n| and
|m| are equal, we want a proof of |n == m| or a proof of |neg (n == m)|.  This
is performed using the equality comparison operator |eq n m|.

While these proofs are very useful in the code, having to convert from a proof
to a Boolean explicitly clutters up the code and does not aid in understanding.
As such, we will (especially in \autoref{chp:introduction}) understand |eq n m|
as |true| if |n| and |m| are equal and |false| otherwise.  This is purely a
matter of syntactic convenience, but makes the code read much more naturally.
The proper way of writing this would be |isYes (eq n m)|.

\section{Monads}

In a purely functional programming language such as Agda, functions are pure:
they produce a single output based on their input, deterministically.  However,
sometimes we wish for a function to do more: for example, to also make use of
some state.  An ingenious approach to this problem is to make use of the
structure of monads~\cite{monadsforfp}.

The situation is best illustrated by an example.  The product-exponent
adjunction gives rise to a monad |State S A = S -> (S * A)|.  In addition to the
action on morphisms (denoted |fmap|), unit (denoted |return|) and multiplication
(denoted |join|), we can construct the following monadic actions:
\begin{code}
_>>=_ : State S A -> (A -> State S B) -> State S B
a >>= f = join (fmap f a)

_>>_ : State S A -> State S B -> State S B
a >> b = a >>= const b

get : State S S
get = \ s -> s , s

set : S -> State S top
set s = \ _ -> s , tt
\end{code}

This allows us to write code like the following:
\begin{code}
counter : State Nat Nat
counter =  get >>= \ n
           set (n + 1) >>
           return (n + 1)
\end{code}

We can use this to encode stateful programs in a functional programming
language.  However, the notation is somewhat unfortunate.  Agda therefore
provides us with a syntactic sugar, using which we can write the above as
follows:
\begin{code}
counter : State Nat Nat
counter = do
  n <- get
  set (n + 1)
  return (n + 1)
\end{code}

Apart from the state monad, numerous others have been found to be useful.  A
number of examples are covered by Moggi~\cite{compnotions}.
