\chapter{Proof Techniques}

We now wish to define a similarity relation between games.  We define this
purely in terms of what we require hold for this relation.  In the next chapter,
we will show that these conditions are indeed satisfied when we provide an
interpretation of |CryptoExpr| terms.

% In a sense, we cannot speak about indistinguishability without mentioning
% interpretations because oracle implementations only exist within a certain
% monad.  

Note that we did not specify the implementation of an oracle as part of the game
syntax in the above.  This because the oracle has access to operations that
the adversary should not be able to access; in particular, the oracle may have
state that it can read and write, which the adversary should not be able to do.
In practice, a notion of similarity between games should allow for a difference
in the oracle implementation.
