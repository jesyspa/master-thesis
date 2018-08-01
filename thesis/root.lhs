\documentclass{report}

\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{amsfonts}
\usepackage{amsthm}
\usepackage{array}
\usepackage{todonotes}
\usepackage[margin=4cm]{geometry}
\usepackage{appendix}
\usepackage{hyperref}
\newcommand*{\Appendixautorefname}{appendix}

%include polycode.fmt
%include agda.lhs
%include localdefs.lhs

\newcommand{\abs}[1]{\left|| #1 \right||}
\newcommand{\norm}[1]{\left\lVert #1 \right\rVert}
\newcommand{\clink}[1]{\href{http://github.com/jesyspa/master-thesis/tree/master/src/#1.agda}{\nolinkurl{#1}}}
\newcommand{\cf}[1]{c.f.~\clink{#1}}

\DeclareMathOperator{\PreMGL}{\mathbf{Pre-MGL}}
\DeclareMathOperator{\MGL}{\mathbf{MGL}}

\newtheorem{theorem}{Theorem}
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definition}
\newtheorem{remark}{Remark}

\title{Master Thesis: Formalisation of Cryptographic Proofs in Agda}
\author{By Anton Golov,\\under the supervision of\\Jaap van Oosten, Wouter
Swierstra, and Victor Cacciari Miraldo}

\begin{document}
    \maketitle

    \begin{abstract}
        The game-based style of proofs~\cite{codebasedgames, gameexamples} is
        often used in cryptography to prove properties of cryptographic
        primitives, such as the security of an encryption scheme.  Given the
        importance of cryptography in the modern world, there is considerable
        value in being able to verify these proofs automatically.  In this
        thesis, we develop a system for expressing proofs of this form in the
        Agda programming language.
    \end{abstract}

    \tableofcontents

    %include chapters/foreword.lhs
    %include chapters/01-introduction.lhs
    %include chapters/02-games.lhs
    %include chapters/03-proofs.lhs
    %include chapters/04-interpretation.lhs
    %include chapters/05-command-structures.lhs
    %include chapters/06-indexed-monads.lhs
    %include chapters/07-crypto-language.lhs

    \begin{appendices}
        %include chapters/ap01-notation.lhs
    \end{appendices}

    \nocite{*}
    \bibliography{thesis}
    \bibliographystyle{alpha}
\end{document}
