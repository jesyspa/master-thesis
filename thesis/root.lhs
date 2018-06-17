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

    \begin{appendices}
        %include chapters/ap01-finite-sets.lhs
        %include chapters/ap02-rationals.lhs
        %include chapters/ap03-distributions.lhs
        %include chapters/ap04-code.lhs
    \end{appendices}

    \nocite{*}
    \bibliography{thesis}
    \bibliographystyle{alpha}
\end{document}
