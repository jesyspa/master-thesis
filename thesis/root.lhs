\documentclass{report}

\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{amsfonts}
\usepackage{amsthm}
\usepackage{array}
\usepackage{hyperref}
\usepackage{todonotes}
\usepackage[margin=4cm]{geometry}
\usepackage{appendix}
\newcommand*{\Appendixautorefname}{appendix}

%include polycode.fmt
%include agda.lhs
%include localdefs.lhs

\newcommand{\abs}[1]{\left|| #1 \right||}
\newcommand{\norm}[1]{\left\lVert #1 \right\rVert}

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
        When we use cryptographic algorithms, we rely that they provide the
        security guarantees they claim.  We develop a system for reasoning about
        such guarantees in the Agda programming language.
    \end{abstract}

    \tableofcontents

    %%include chapters/foreword.lhs
    %include chapters/01-introduction.lhs
    %include chapters/02-games.lhs
    %include chapters/03-proofs.lhs
    %include chapters/04-command-structures.lhs
    %include chapters/05-interpretation.lhs
    %include chapters/06-indexed-monads.lhs
    %include chapters/08-crypto-language.lhs

    \begin{appendices}
        %include chapters/ap01-notation.lhs
    \end{appendices}

    \nocite{*}
    \bibliography{thesis}
    \bibliographystyle{alpha}
\end{document}
