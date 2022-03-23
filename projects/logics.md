# Predicate, modal, and temporal logics

This file contains 3 projects, depending on which extension X to the
propositional logic from lectures/exercises you choose.

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

## Suggested background reading materials

A good general reference for different kinds of logics, their syntax,
and semantics is the book "Logic in Computer Science" by Huth & Ryan
([link](https://www.cs.bham.ac.uk/research/projects/lics/)).

### Predicate logic

* Week 5-6 lecture notes

  - overview of propositional and predicate logics, natural deduction,
    semantics

  - note: differently from lectures, where structural properties (of
    weakening, contraction, and exchange) were included as rules in
    their own right, in this project you will define a natural
    deduction proof system in which they are admissible

* Chapter 2 of Logic in Computer Science (Huth & Ryan)

  - syntax, proof theory, and semantics of predicate logic

  - note: the natural deduction rules are presented in a graphical
    style; in the project you will be using the sequent-style used in
    the lecture notes

* Sections 3.3-3.8 of the Homotopy Type Theory Book (https://homotopytypetheory.org/book/)

  - overview how propositions are characterised in (homotopy) type
    theory

  - overview how predicate logic formulae are interpreted as types in
    type theory using the help of propositional truncation to hide the
    witnesses of disjunctions and existential quantifiers

* Section 4.1 of Categorical Logic and Type Theory (Jacobs)

  - presents in detail the full sequent-style natural deduction system
    for predicate logic

### Modal logic

* Chapter 5 of Logic in Computer Science (Huth & Ryan)

  - syntax, proof theory, and (Kripke) semantics of modal logics

  - note: the natural deduction rules are presented in a graphical
    style; in the project you will be using the sequent-style rules
    similar to the ones used for propositional logic in the lectures

  - note: differently from lectures, where structural properties (of
    weakening, contraction, and exchange) were included as rules in
    their own right, in this project you will define a natural
    deduction proof system in which they are admissible

* Fitch-Style Modal Lambda Calculi (Clouston) (https://arxiv.org/pdf/1710.08326.pdf)

  - Fitch-style natural deduction systems for modal lambda calculi

  - for the project, you will use the propositions as types
    correspondence to recover a natural deduction system for
    propositional modal logic(s) (S4 in first instance)

* Chapter 4 of The Proof Theory and Semantics of Intuitionistic Modal
  Logic (Simpson) (https://era.ed.ac.uk/handle/1842/407)

  - labelled natural deduction system for (intuitionistic) modal logic

  - note: this would be used if for some reason the Fitch-style natural
    deduction system and its proof rules cause problems

### Temporal logic

* Labeled Natural Deduction for Temporal Logics (Volpe)
  (https://www.math.tecnico.ulisboa.pt/~mvolpe/publications/theses/volpe-phd-thesis.pdf)

  - (this is a good starting point for the project)

  - Section 2.3.4 presents the syntax and semantics of LTL
  
  - Section 2.3.4 also presents Hilbert-style axioms of LTL which you should
    verify both using the semantics, and later also using natural deduction
    
  - Section 4.2.4 presents a labelled natural deduction system for LTL
    (without the until modality)
  
  - Section 4.4 gives a proposal how to also incorporate the until modality
    in the natural deduction system

* Section 3.2 of Logic in Computer Science (Huth & Ryan)

  - syntax and semantics of LTL

* Natural Deduction Calculus for Linear-Time Temporal Logic (Bolotov et al.)
  (https://link.springer.com/chapter/10.1007/11853886_7)

  - natural deduction system for (intuitionsitic) LTL (using abstract
    labels)

  - semantics of LTL

* Constructive linear-time temporal logic: Proof systems and Kripke
  semantics (Kojima and Igarashi)
  (https://www.sciencedirect.com/science/article/pii/S0890540111001416)

  - natural deduction system for (intuitionsitic) LTL (using time-tick
    labels)

  - semantics of LTL

  - considers LTL with only the next modality
