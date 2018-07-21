\chapter*{Foreword}

My interests have always been somewhere between mathematics and computer
science, and this thesis falls between them pretty neatly.  As such, I apologise
to the mathematicians for the lack of rigour, and to the computer scientists for
the lack of practical applicability.

A thorough introduction to Agda and category theory is beyond the scope of this
thesis, so I refer the reader to TODO FIND REFERENCES.  I am not using any
particularly advanced Agda features.  Agda code tends to look like this:
\begin{code}
name : Type
name = body
\end{code}
This specifies that |name| is of type |Type| and is by definition equal to
|body|.  We can pattern match on arguments, we can introduce data types\ldots
So, yeah, it's too much to put here, I think.

From category theory we mostly use the notion of a functor and a monad.  Still,
the text is way more understandable if you know how functor categories work, but
it's still all very basic.  Oh, and we use Kan extensions once in a while, you
don't mind, do you?

I would like to thank a whole bunch of people; Wouter, Victor, Jaap, Napoleon,
dstolfa (Freenode, Kan extension stuff).

\section*{List of Notation}

\begin{itemize}
\end{itemize}
