\section{Timetable and Planning}
\label{sec:timetable}

This project started December 2017 and must be complete by August 2018.  I have spent December and January developing
the version of the framework presented here, and February and March writing this proposal.

\begin{table}
    \centering
    \begin{tabular}[h]{m{1.5cm} || p{9cm}}
        Month    & \centering\arraybackslash Goal \\
        \hline
        December & \\
        January  & Create a proof-of-concept implementation. \\
        February & \\
        March    & \\
        April    & Finish and submit this research proposal.   Define a notion of $\epsilon$-indistinguishability.\\
        May      & Show that $\epsilon$-indistinguishability is preserved by basic operations on distributions and
                   introduce computations involving oracles. \\
        June     & Formalise existing proofs in the developed system.\\
        July     & Prepare a final draft of the thesis.\\
        August   & Finish and present the thesis.
    \end{tabular}
    \caption{Timetable Summary}
\end{table}

Going forward, I would like to spend the remainder of April working on finding a suitable notion of
$\epsilon$-indistinguishability, since the rewriting rules we obtain from that will be crucial in determining what
presentations of games are and aren't viable.  I will spend May figuring out how this notion can be made to work
together with computations involving oracles, and implementing the features necessary to express proofs in this style.
June will be spent formalising existing proofs in this style to show that it is in fact workable and writing the thesis.
The last will continue into July and August, together with bugfixing.

While implementing a proof search algorithm that could use reflection to simplify the arguments would be a useful
addition to this project, it is unlikely that there will be time for it.
