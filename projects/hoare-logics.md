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
