# Definitional interpreters for STLC

This file contains 5 projects, depending on which feature X you choose.

## Goals of the project

* Define a (monadic) definitional interpreter for the simply typed
  lambda calculus (STLC) extended with feature(s) X.

* Features X you can choose from (you can also suggest your own):
  1. sum types and algebraic data types
  2. exceptions and state
  3. exceptions and nondeterminism
  4. algebraic effects and effect handlers
  5. natural numbers and primitive recursion, and
     also general recursion (using the delay monad for the latter)

* Define the equational theory for STLC + X.

* Prove that the definitional interpreter is sound (that it validates
  the equational theory).

* A simpler variant of this project will involve defining the
  definitional interpreter into a shallow monad in Agda. A more
  advanced version of this project will involve you using
  [Agda's categories library](https://github.com/agda/agda-categories).
