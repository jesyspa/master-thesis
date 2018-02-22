\documentclass{report}
%include lhs2TeX.fmt
%include agda.lhs


\title{Research Proposal: Formalisation of Cryptographic Proofs in Agda}
\author{By Anton Golov,\\under the supervision of\\Jaap van Oosten, Wouter Swiestra, and Victor Miraldo}

\begin{document}
    \maketitle

    \begin{abstract}
        Given an encryption scheme, it is desirable to show that it is secure against particular forms of attack.  For
        my thesis, I wish to develop a library for the Agda programming language which would aid in expressing proofs of
        this nature.
    \end{abstract}
    \tableofcontents

    %include chapters/01-introduction.lhs
    %include chapters/02-distributions.lhs
    %include chapters/03-syntax.lhs
    %include chapters/04-crypto-games.lhs
    %include chapters/05-further-work.lhs

    \bibliography{proposal}
    \bibliographystyle{alpha}
\end{document}
