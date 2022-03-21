# Hoare logics for WHILE (and STLC)

This file contains 3 projects, depending on which feature X you choose.

## Source material

A good general reference for different kinds of logics (including
Hoare Logic) is the book "Logic in Computer Science" by Huth & Ryan
([link](https://www.cs.bham.ac.uk/research/projects/lics/)).

## Goals of the project

* Define a deep embedding of a small imperative programming language
  (commonly called the WHILE language) extended with feature(s) X.

* Features X you can choose from (you can of course suggest your own):
  1. state and exceptions
  2. state and input/output
  3. state and nondeterminism

* Define a deep embedding of Hoare Logic for WHILE + X.

* Define a definitional interpreter for WHILE + X.

* Prove that the Hoare Logic is sound with respect to the definitional
  interpreter.

* Possible extension: extend WHILE + X and the Hoare Logic to the simply
  typed lambda calculus (STLC) + X by using Hoare Types/Hoare Monad to
  encode the Hoare triples at the level of STLC's type system.

* A simpler variant of this project will involve defining the
  definitional interpreter into a shallow (graded or parameterised) monad
  in Agda. A more advanced version of this project will involve you using
  [Agda's categories library](https://github.com/agda/agda-categories).

## Suggested background reading materials

A good general reference for different kinds of logics, their syntax,
and semantics is the book "Logic in Computer Science" by Huth & Ryan
([link](https://www.cs.bham.ac.uk/research/projects/lics/)).

A good general reference for different kinds of lambda calculi and
programming language features is Types and Programming Languages
(Pierce) (https://www.cis.upenn.edu/~bcpierce/tapl/).

The definitional interpreter part of the project will take the form of
an interpretation function from well-typed programs into Agda types
(wrapped in a (parameterised) monad; and into a suitable category, if
using the categories library). For this, see the lecture notes and
exercises on the semantics of propositional logic, together with the
propositions as types correspondence.

### WHILE and Hoare Logic

* Chapter 4 of Logic in Computer Science (Huth & Ryan)

  - overview of program verification in general

  - syntax of the WHILE language

  - syntax of Hoare triples

  - proof calculus / deduction system for Hoare logic

### State, exceptions, IO, and nondeterminism effects/monads

* Notions of Computation and Monads (Moggi)
  (https://www.cs.cmu.edu/~crary/819-f09/Moggi91.pdf)

  - an overview of different kinds of computational effects and
    the monads that naturally model them

  - also gives an overview of the basic programming abstractions
    for effectful programming based on monads

### Parameterised monads

* Parameterised Notions of Computation (Atkey)
  (https://bentnib.org/paramnotions-jfp.pdf)

  - definition of a notion of parameterised monads

  - useful if you want to state the definitional interpreter and
    correctness results with respect to an abstract interface of
    effectful computations
