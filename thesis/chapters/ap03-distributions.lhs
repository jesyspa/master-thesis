\chapter{Probability Distributions}

This appendix can basically be a massive info dump showing exactly what we
require of distributions and how we prove it.

\section{The |Dist| Monad}

Agda code, lots of Agda code.  Occasional remarks on why constraints in certain
places are necessary.

\section{Informal Proofs}

A bunch of properties are very annoying to prove in Agda.  We may want to still
check that they hold; prime examples are interactions between
$\epsilon$-indistinguishability and binding.  In particular, the analysis of
how similar |f| and |g| have to be for |x >>= f| and |x >>= g| to be
$\epsilon$-indistinguishable is important.

\section{The Effect of State}

Applying a state monad transformer on top of |Dist| could upset
indistinguishability, we should at least briefly argue that this does not
happen.
