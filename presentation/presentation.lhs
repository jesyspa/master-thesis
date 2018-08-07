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
\begin{itemize}
    \item Cryptographic Proofs are Hard
    \item TODO
\end{itemize}
\end{frame}

%{
\begin{frame}
\frametitle{One-Time Pad}
%format keygen = "\F{keygen}"
%format encrypt = "\F{encrypt}"
%format decrypt = "\F{decrypt}"
Consider the following encryption scheme:
\begin{code}
keygen : (n : Nat) -> Rand (BitVec n)
keygen n = uniform n

encrypt : (FORALL n) -> BitVec n -> BitVec n -> BitVec n
encrypt v w = (xor v w)

decrypt = encrypt
\end{code}
\pause
Question: How can we express that this scheme is secure?
\end{frame}

\begin{frame}
\frametitle{Games}

\end{frame}
%}

\begin{frame}
\frametitle{Code-Based Games}

\end{frame}

\begin{frame}
\frametitle{}
\end{frame}

\section{Formalising $\epsilon$-Indistinguishability}

\begin{frame}
\frametitle{Expressing Games}
\begin{code}
data CryptoExpr : 
\end{code}
\end{frame}

\begin{frame}
\frametitle{Expressing Games}
\end{frame}

\begin{frame}
\frametitle{Expressing }
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
