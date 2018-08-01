# master-thesis

This is the code accompanying the master thesis.  Since several design choices we could make were incompatible, the code
consists of several independent experiments that rely on some common code.

The common functionality is contained in the following directories:
* `Algebra/`: Tools for reasoning
* `Utility/`: Additional data structures.  In particular:
    - `Utility/List/`: Various lemmas about list operations.
    - `Utility/List/Elem/`: Type for reasoning about list membership.
    - `Utility/List/Lookup/`: Various lemmas for reasoning about lists of key-value pairs.
    - `Utility/Vector/`: Various operations and lemmas for operating with vectors.
    - `Utility/State/`: Indexed versions of the state monad.
    - `Utility/Writer/`: An implementation of the writer monad.
* `Probability/`: Typeclass for types that represent probabilities.
* `Ditribution/`: Typeclass for probability distribution monads.
* `Interaction/`: A number of experiments on interaction and command structures.  In particular:
    - `Interaction/Indexed/`: The normal interaction structure overview.
* `Crypto/`: A formalisation of some simple properties.
    - `Crypto/OTP.agda`: A proof of IND-EAV for OTP.
* `Synthetic/`: A syntactic formalisation; closest to the text.
