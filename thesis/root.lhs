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

\newcommand{\HRule}{\rule{\linewidth}{0.5mm}}

\begin{document}
    % Thanks to Sven for providing the title page code.
    \begin{titlepage}
        \begin{center}
            \includegraphics[width=0.6\textwidth]{./logo.png}~\\[2.5cm]
            \textsc{\Large Department of Mathematics}\\[0.5cm]
            \textsc{\Large Master Thesis}\\[0.5cm]
            \HRule \\[0.4cm]
            { \huge \bfseries Formalisation of Cryptographic Proofs in Agda \\[0.4cm] }
            \HRule \\[1.5cm]
            \noindent
            \begin{minipage}[t]{0.4\textwidth}
            \begin{flushleft} \large
            \emph{Author:}\\
            Anton \textsc{Golov}
            \end{flushleft}
            \end{minipage}%
            \begin{minipage}[t]{0.4\textwidth}
            \begin{flushright} \large
            \emph{Supervisors:} \\
            Dr.~Jaap \textsc{van Oosten}
            Dr.~Wouter \textsc{Swierstra}\\
            Victor \textsc{Cacciari Miraldo}
            \end{flushright}
            \end{minipage}

            \vspace{+100pt}
            {\large December 2017-August 2018}
        \end{center}
    \end{titlepage}

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

    \bibliography{thesis}
    \bibliographystyle{alpha}
\end{document}
