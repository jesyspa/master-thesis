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

We can express properties as games between a challenger and an adversary.~\cite{codebasedgames}\pause

Two ways of looking at this:
\begin{itemize}
  \item A system of players communicating with each other; \pause and
  \item Two situations that the adversary has to distinguish.
\end{itemize}\pause

The challenge is to capture both in one system!
\end{frame}

\begin{frame}
\frametitle{Agda}

Agda is a dependently type functional programming language.
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
record CmdStruct : Set1 where
  field
    Command : Set
    Response : Command -> Set
\end{code}
\end{block}
\end{frame}

\begin{frame}
\frametitle{Expressing Computations}
\begin{block}{Free Monad}
\begin{code}
data FreeMonad (C : CmdStruct) : Set -> Set where
  ReturnFM  : A -> FreeMonad C A
  InvokeFM  : (c : Command C) -> (Response C c -> FreeMonad C A) -> FreeMonad C A
\end{code}
\end{block}
\pause
\begin{block}{Monadic Structure}
\begin{code}
fmapFM : (A -> B) -> FreeMonad C A -> FreeMonad C B
fmapFM f (ReturnFM a) = ReturnFM (f a)
fmapFM f (InvokeFM c cont) = InvokeFM c \ r -> fmapFM f (cont r)

bindFM : FreeMonad C A -> (A -> FreeMonad C B) -> FreeMonad C B
bindFM (ReturnFM a)       f = f a
bindFM (InvokeFM c cont)  f = InvokeFM c \ r -> bindFM (cont r) f
\end{code}
\end{block}
\end{frame}

\begin{frame}
\frametitle{Expressing Games}
Let |ST| be some state type.
\begin{block}{Cryptographic Computations}
\begin{code}
data CryptoCmd : Set where
  Uniform   : Nat  ->  CryptoCmd
  GetState  :          CryptoCmd
  SetState  : ST   ->  CryptoCmd

CryptoCS : CmdStruct
Command   CryptoCS = CryptoCmd
Response  CryptoCS (Uniform n)   = BitVec n
Response  CryptoCS GetState      = ST
Response  CryptoCS (SetState _)  = top
\end{code}
\end{block}
\end{frame}

\begin{frame}
\frametitle{Expressing Indistinguishability}

We relate games by an inductively defined family of relations |==eE| indexed by a non-negative rational
$\epsilon$.\pause
\end{frame}

\begin{frame}
\frametitle{Showing Consistency}
How do we know |==eE| isn't trivial?
\pause

We can make a model of our logic where |return true|, |coin|, and |return false| are distinct!
\pause

We represent a probability distribution over |A| as a list of |A * Q| pairs.
\end{frame}
\begin{frame}
\frametitle{Multiplayer Systems}
\begin{block}{Command Structure Implementations}
\begin{code}
Implementation : (C1 C2 : CmdStruct) -> Set
Implementation C1 C2 = (c : Command C1) -> FreeMonad C2 (Response C1 c)
\end{code}
\end{block}
Intuitively: a way of translating |C1| programs into |C2| programs.
\end{frame}

\begin{frame}
\frametitle{Multiplayer Systems (\emph{cont.})}
\begin{block}{Combining Command Structures}
\begin{code}
_+CS_ : (C1 C2 : CmdStruct) -> CmdStruct
Command   (C1 +CS C2) = Command C1 + Command C2
Response  (C1 +CS C2) (left   c) = Response C1 c
Response  (C1 +CS C2) (right  c) = Response C2 c
\end{code}
\end{block}
\end{frame}

\begin{frame}
\frametitle{Multiplayer Systems (\emph{cont.})}
We can use this to express systems with multiple players.\pause

This lets us take
\begin{code}
Impl A (B +CS C +CS X)
Impl B (C +CS X)
Impl C X
\end{code}
and get
\begin{code}
Impl (A +CS B +CS C) X
\end{code}
\end{frame}

\begin{frame}
\frametitle{Why does this work?}
The interaction between |_+CS_|, |Implementation|, and |FreeMonad| is so nice.  Why?\pause
\begin{block}{Command Structure Morphisms}
\begin{code}
record CmdMorphism (C1 C2 : CmdStruct) : Set where
  CommandF   : Command C1 -> Command C2
  ResponseF  : Response C2 (CommandF c) -> Response C1 c
\end{code}
\end{block}
\pause

|_+CS_| is a coproduct and |FreeMonad| is (morally) a left adjoint, so preserves coproducts.  |Implementation|s
are transposes.
\end{frame}

\section{Indexed Monads}

\begin{frame}
\frametitle{Indexed Monads}
Indexed monads~\cite{indexedmonads} let us express a computation that is in a certain state.
\begin{code}
  returni : A i -> M A i
  bindi : M A i -> ((FORALL j) -> A j -> M B j) -> M A j
\end{code}
\pause

Examples:
\begin{itemize}
  \item Indexed state: |State| with a modifiable type.
  \item Use counter: bound number of times an operation may be used.
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{Generalising Command Structures}
\begin{block}{Interaction Structures}
\begin{code}
record IStruct (S : Set) : Set where
  field
    Command   : S -> Set
    Response  : {s : S} -> Command s -> Set
    next      : {s : S}(c : Command s)(r : Response c) -> S
\end{code}
\end{block}
\end{frame}

\begin{frame}
\frametitle{Difficulties}
\begin{itemize}
  \item The categorical structure of interaction structures is not as nice.\pause
  \item Programming with interaction structures is very verbose.\pause
  \item Constraints are part of the structure, cannot be added later.
\end{itemize}
\end{frame}

\section{Conclusions}

\begin{frame}
\frametitle{Usability}
Theoretically, the system we have can express a wide variety of proofs.  But:\pause
\begin{itemize}
  \item Many trivial steps must be written out explicitly.\pause
  \item Specifying a step is very verbose.\pause
  \item Especially in the indexed case, argument deduction does not go very far.
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{Future Work}
Work necessary to make a usable system:\pause
\begin{itemize}
  \item Generalisation of $\epsilon$-indistinguishability to multiplayer systems.\pause
  \item Formalisation of more proof techniques.\pause
\end{itemize}

Possible extensions:\pause
\begin{itemize}
  \item Introduction of tactics.\pause
  \item Non-embedded DSL for multiplayer systems.
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{Summary}
In this project, we have
\begin{itemize}
  \item Expressed cryptographic algorithms in Agda;
  \item Developed a proof system for reasoning about their properties;
  \item Captured the notion of a model of this logic;
  \item Partially developed such a model, identifying key issues; and
  \item Discovered several applications of indexed monads in this domain.
\end{itemize}\pause

\centering
Thank you!
\end{frame}

\begin{frame}
\frametitle{Bibliography}
\bibliography{presentation}
\bibliographystyle{alpha}
\end{frame}
\end{document}
