\documentclass{article}

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

\title{Research Proposal: Formalisation of Cryptographic Proofs in Agda}
\author{By Anton Golov,\\under the supervision of\\Jaap van Oosten, Wouter Swiestra, and Victor Miraldo}

\begin{document}
    \maketitle

    \begin{abstract}
        Given an encryption scheme, it is desirable to show that it is secure against particular forms of attack.  For
        my thesis, I wish to develop a library for the Agda programming language which would aid in expressing proofs of
        this nature.
    \end{abstract}

    %include chapters/sp1-introduction.lhs
    %include chapters/sp2-proofs.lhs
    %include chapters/sp3-implementation-outline.lhs
    %include chapters/sp4-research-plan.lhs
    %include chapters/sp5-timetable.lhs

    \nocite{*}
    \bibliography{proposal}
    \bibliographystyle{alpha}
\end{document}
