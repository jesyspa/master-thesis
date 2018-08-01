\chapter*{Foreword}

The goal of this research project was initially to develop a system for
cryptographic proofs in the Agda programming language.  During the process, it
became clear that the construction of the system as a whole would not be
feasible, and the project thus became a number of experiments in Agda that were
each intended to investigate a particular feature of the design space.

The purpose of this thesis is to write up the results of these experiments and
show how they can be brought together.  The code is available on
GitHub\footnote{\url{https://github.com/jesyspa/master-thesis}}, and the text
will contain references to the files where relevant.\footnote{All references are
to Agda files in the above repository, relative to the \texttt{src} directory.
For example \texttt{Probability/Class} refers to the file
\url{https://github.com/jesyspa/master-thesis/tree/master/src/Probability/Class.agda}.}

Since formalisation in Agda is the point of the research, I assume that the
reader is familiar with the Agda programming language.  There are several good
introductions online, for example by Ulf Norell~\cite{agdatut}.  For later
chapters, a passing familiarity with category theory is also beneficial.

I would like to thank dr.~Wouter Swierstra for agreeing to be my supervisor
(despite my thesis being in maths), and, together with Victor Cacciari Miraldo,
for their time and advice throughout the project.  I would also like to thank
dr.~Jaap van Oosten, my tutor and second supervisor, for allowing me to do this
project (despite my master's being in maths), and for his guidance throughout
the years of my master's degree.

\begin{flushright}
  Anton Golov\\
  27 July, 2018
\end{flushright}

