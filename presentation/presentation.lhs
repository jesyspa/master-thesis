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
\begin{itemize}
    \item The Problem
    \item Code-Based Games
    \item Logic and Agda
    \item Our Work: Formalisation of Indistinguishability
    \item Soundness
    \item Future Work
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{The Problem}
Interesting cryptographic properties:
\begin{itemize}
    \item TODO: Come up with some
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
\frametitle{Security}

\end{frame}
%}

\begin{frame}
\frametitle{Code-Based Games}
\begin{code}
\end{code}
\end{frame}

\begin{frame}
\frametitle{}
\end{frame}

\begin{frame}
\frametitle{}
\end{frame}

\begin{frame}
\frametitle{}
\end{frame}

\end{document}
