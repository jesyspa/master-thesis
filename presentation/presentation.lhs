\documentclass{beamer}

\usepackage[utf8]{inputenc}

\title{Formalising Cryptographic Proofs in Agda}
\author[Golov, Swierstra, Cacciari Miraldo, Van Oosten]
{A. Golov, W. Swierstra, V. Cacciari Miraldo, J. Van Oosten}
\institute{Utrecht University}

%include polycode.fmt
%include agda.lhs
%include localdefs.lhs


\begin{document}
\frame{\titlepage}

\begin{frame}
\frametitle{The Plan}
\tableofcontents
\end{frame}

\section{The Problem}

\begin{frame}
\frametitle{The Problem}
Guaranteeing properties of cryptographic primitives is important.
\pause

How can we check their proofs automatically?
\pause

What does a proof look like?
\end{frame}

\begin{frame}
\frametitle{Game-Based Proofs}

We can express properties as games between a challenger and an adversary.\pause

Two ways of looking at this:
\begin{itemize}
  \item A system of players communicating with each other; \pause and
  \item Two situations that the adversary has to distinguish.
\end{itemize}\pause

The challenge is to capture both in one system!
\end{frame}

\begin{frame}
\frametitle{Agda}

Agda is a dependently type programming language.
\pause

Why Agda?
\pause
\begin{itemize}
  \item Fairly similar to $\lambda\Pi$.\pause
  \item Encourages programming with dependent types.\pause
  \item Fairly similar to Haskell.
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{The Problem}
So, our goals:
\begin{itemize}
  \item Express cryptographic primitives in Agda.\pause
  \item Express an indistinguishability relation.\pause
  \item Express multiplayer systems.
\end{itemize}
\end{frame}

\section{Formalising $\epsilon$-Indistinguishability}

\begin{frame}
\frametitle{Expressing Computations}

How can we express computations that have access to extra commands?\pause

\begin{block}{Command Structures}
\begin{code}
TODO
\end{code}
\end{block}
\end{frame}

\begin{frame}
\frametitle{Expressing Games}

Free monads
\end{frame}

\begin{frame}
\frametitle{Expressing Indistinguishability}

Syntactic relation
\end{frame}

\begin{frame}
\frametitle{Soundness}


\end{frame}

\section{Bonus Material}

\begin{frame}
\frametitle{Command Structures}
\begin{code}
record CmdStruct : Set1 where
  field
    Command : Set
    Response : Command -> Set
\end{code}
\end{frame}

\section{Conclusions}

\begin{frame}
\frametitle{}
\end{frame}

\end{document}
