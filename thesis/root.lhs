\documentclass{report}

\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{amsfonts}
\usepackage{amsthm}
\usepackage{array}
\usepackage{hyperref}
\usepackage{todonotes}

%include polycode.fmt
%include agda.lhs
%include localdefs.lhs

\newcommand{\abs}[1]{\mid\! #1 \!\mid}

\newtheorem{theorem}{Theorem}
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\theoremstyle{definition}
\newtheorem{definition}{Definition}

\title{Master Thesis: Formalisation of Cryptographic Proofs in Agda}
\author{By Anton Golov,\\under the supervision of\\Jaap van Oosten, Wouter Swiestra, and Victor Miraldo}

\begin{document}
    \maketitle

    \begin{abstract}
        When we use cryptographic algorithms, we rely that they provide the
        security guarantees they claim.  We develop a system for reasoning about
        such guarantees in the Agda programming language.
    \end{abstract}

    \tableofcontents

    %include chapters/01-introduction.lhs
    %include chapters/02-games.lhs
    %include chapters/03-interpretation.lhs
    %include chapters/04-proofs.lhs
    %include chapters/05-indexed-monads.lhs
    %include chapters/06-interaction-structures.lhs
    %include chapters/07-crypto-language.lhs

    \nocite{*}
    \bibliography{thesis}
    \bibliographystyle{alpha}
\end{document}
