# Predicate, modal, and temporal logics

This file contains 3 projects, depending on which extension X to the
propositional logic from lectures/exercises you choose.

## Source material

A good general reference for different kinds of logics, their syntax,
and semantics is the book "Logic in Computer Science" by Huth & Ryan
([link](https://www.cs.bham.ac.uk/research/projects/lics/)).

## Goals of the project

* Extend the deeply embedded propositional logic, its semantics, and
  the soundness proof from the lectures/exercises with feature X.

* Extensions X you can choose from (you can of course suggest your own):

  1. **predicate logic** over natural numbers (in detail, this means
     adding universal and existential quantifiers over natural number
     variables to the logic; natural number typed terms; and an
     equality predicate between natural number typed terms)

  2. propositional **modal logic(s)** with necessity (box) and possibility
     (diamond) modalities (in detail, this means extending the logic with 
     modalities; and adapting the natural deduction proof system accordingly,
     e.g., by following [this PhD thesis](https://era.ed.ac.uk/handle/1842/407)
     or by following [this article](https://arxiv.org/abs/1710.08326))

  3. **linear time temporal logic** (in detail, this means extending the
     logic with modalities of temporal logic; and adapting the natural
     the natural deduction proof system accordingly, e.g., by following
     [this article](https://link.springer.com/chapter/10.1007/11853886_7))

* If you choose (1), then you will also show how to express the Peano
  axioms in the deeply embedded logic, together with showing how to
  use them to prove properties of natural number computations.

* If you choose (2) or (3), then you will instead show how to derive
  various modal or temporal tautologies in the deeply embedded logic,
  and relate validity of various other principles to properties of
  the corresponding semantics. You will also use the deeply embedded
  logic to specify computational system(s) and prove their properties.
  
* A simpler variant of this project will involve defining the
  semantics and interpretation into shallow Agda types. A more
  advanced version of this project will involve you using [Agda's
  categories library](https://github.com/agda/agda-categories).
