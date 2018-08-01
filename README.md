# master-thesis

This is the code accompanying the master thesis.  Since several design choices we could make were incompatible, the code
consists of several independent experiments that rely on some common code.

The common functionality is contained in the following directories:
* `Algebra/`: Various tools for reasoning about abstract structures.
* `Utility/`: A number of useful types.  In particular:
    - `Utility/List/`: Various lemmas about list operations.
    - `Utility/List/Elem/`: Type for reasoning about list membership.
    - `Utility/List/Lookup/`: Various lemmas for reasoning about lists of key-value pairs.
    - `Utility/Vector/`: Various operations and lemmas for operating with vectors.
    - `Utility/State/`: Indexed versions of the state monad.
    - `Utility/Writer/`: An implementation of the writer monad.
* `Probability/`: Typeclass for types that represent probabilities.
* `Distribution/`: Typeclass for probability distribution monads.
    - `Distribution/List/`: An incomplete implementation of the list model.
* `Interaction/`: A number of experiments on interaction and command structures.  In particular:
    - `Interaction/Indexed/`: An implementation of the interaction structures described in the thesis.
    - `Interaction/Simple/`: An implementation of the command structures described in the thesis.
    - `Interaction/Dependent/`: An implementation of interaction structures where the state type is not an index.
    - `Interaction/Relational/`: An implementation with a different notion of interacture structure morphisms.
* `Crypto/`: A formalisation of some simple properties.
    - `Crypto/OTP.agda`: A proof of IND-EAV for OTP.
* `Synthetic/`: A syntactic formalisation; this is closest to the text of the thesis.

The code has been tested with Agda 2.5.4 and Ulf Norell's [agda-prelude](https://github.com/UlfNorell/agda-prelude),
branch `compat 2.5.4`, commit `d193a94bfac9505148cb5cd1b68d08a08260b59c`.
