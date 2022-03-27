# Predicate, modal, and temporal logics

This file contains 3 projects, depending on which extension X to the
propositional logic from lectures/exercises you choose.

## Goals of the project

* Extend the deeply embedded propositional logic, its semantics, and
  the soundness proof from the lectures/exercises with feature X.
  
  - as a warm-up exercise, you should take the propositional logic and 
    its semantics from the exercise classes, and change the semantics
    to be valued in `HProp` instead if `Bool` (see week 6 lecture notes
    and [HProp.agda](agda/HProp.agda) for explanation of `HProp`)

* Extensions X you can choose from (you can of course suggest your own):

  1. **predicate logic** over natural numbers; in detail this means

     - extending the propositional logic from the class with (i) natural
       number typed terms, (ii) quantifiers over natural number typed
       variables, (iii) an equality predicate between natural number
       typed terms
       
       - `t ::= x | zero | suc t | t + t | t * t `
       
       - `phi, psi ::= ... | forall x . phi | exists x . phi | t = t' `

     - giving the resulting logic a semantics
       
       - compared to propositional logic, here you have to consider 
         formulae in context `Gamma |- phi` where `Gamma` is a list
         of natural-number typed variables
         
       - the interpretation of formulae is then given as 
         `[[phi]] : [[Gamma]] -> HProp`

       - you also need to define well-typed terms `Gamma |- t` and 
         define for them an interpretation `[[t]] : [[Gamma]] -> ℕ`
         
       - as the contexts `Gamma` contain variables of only one type,
         they can be represented simply as a natural number `n` (the 
         length of the context), with the variables in terms then 
         being elements of `Fin n` (i.e., De Bruijn indices)

     - validating in Agda that the semantics models Peano axioms
     
       - this means that if `Gamma |- phi` is a Peano axiom, you need 
         to show that for all `g : Gamma`, `proof ([[phi]] g)` is inhabited

     - adapting the natural deduction proof system to account for the
       quantifiers and the equality predicate
       
       - in order to write down the rules for quantifiers and equality, 
         you will also need to define the operations of substituting a
         free variable in a term or formula with another term
       
       - differently from lectures, where structural properties (of
         weakening, contraction, and exchange) were included as rules 
         in their own right, in this project you will define a natural
         deduction proof system in which they are admissible
       
     - giving proofs in the natural deduction system of Peano axioms

     - a good starting point is the lecture notes on predicate logic
       and the propositions-as-types correspondence, together with
       Chapter 2 of "Logic in Computer Science" by Huth & Ryan

  2. propositional **modal logic S4** with necessity (box) and
     possibility (diamond) modalities; in detail, this means:

     - extending propositional logic from the class with modalities 
     
       - `phi, psi ::= ... | □ phi | ◇ phi`

     - giving the resulting logic a Kripke semantics (instead of the
       boolean semantics we gave to propositional logic in the class)
       
       - given a suitable Kripke frame `(W,R,V)`
       
       - the interpretation takes the form `[[phi]] : W -> HProp`

     - validating in Agda that the Kripke semantics models well-known
       tautologies of S4 (see the reference article below)
       
       - this means that for a given tautology `phi`, you need to
         show that for all `w`, `proof ([[phi]] w)` is inhabited

     - adapting the natural deduction proof system to account for the
       modalities (see the reference article below)

       - differently from lectures, where structural properties (of
         weakening, contraction, and exchange) were included as rules 
         in their own right, in this project you will define a natural
         deduction proof system in which they are admissible

     - giving proofs in the natural deduction system of the well-known
       tautologies of S4 (see the reference article below)

     - a good starting point is the article
       "On an Intuitionistic Modal Logic" by Bierman and de Paiva
       (https://link.springer.com/article/10.1023/A:1005291931660)

       - Section 2 presents the syntax of intuitionistic modal logic S4

       - Section 2 presents a list of tautologies of S4

       - Section 4 presents a natural deduction proof system for S4

       - the Kripke semantics for a logic with box and diamond modalities
         can be e.g. found at https://en.wikipedia.org/wiki/Modal_logic

  3. propositional **linear time temporal logic (LTL)** with always,
     next, and until modalities; in detail this means

     - extending propositional logic from the class with modalities
     
       - `phi, psi ::= ... | G phi | X phi | phi U psi`

     - giving the resulting logic a Kripke semantics (instead of the
       boolean semantics we gave to propositional logic in the class)
       
       - given a valuation `V` of atomic formulae at different times
       
       - the interpretation takes the form `[[phi]] : ℕ -> HProp`

     - validating in Agda that the Kripke semantics models well-known
       tautologies of LTL (see the reference material below)

       - this means that for a given tautology `phi`, you need to
         show that for all `n`, `proof ([[phi]] n)` is inhabited

     - adapting the natural deduction proof system to account for the
       modalities (see the reference material below)

       - differently from lectures, where structural properties (of
         weakening, contraction, and exchange) were included as rules 
         in their own right, in this project you will define a natural
         deduction proof system in which they are admissible

     - giving proofs in the natural deduction system of the well-known
       tautologies of LTL (see the reference material below)

     - a good starting point is the PhD thesis "Labeled Natural
       Deduction for Temporal Logics" of Volpe
       (https://www.math.tecnico.ulisboa.pt/~mvolpe/publications/theses/volpe-phd-thesis.pdf)

       - Section 2.3.4 presents the syntax and semantics of LTL
  
       - Section 2.3.4 also presents axioms/tautologies of LTL
    
       - Section 4.2.4 presents a labelled natural deduction system
         for LTL (without the until modality)
  
       - Section 4.4 shows how to also incorporate the until modality
         in the natural deduction system
  
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

### Modal logic (S4)

* Chapter 5 of Logic in Computer Science (Huth & Ryan)

  - syntax, proof theory, and (Kripke) semantics of modal logics

  - note: the natural deduction rules are presented in a graphical
    style; in the project you will be using the sequent-style rules
    similar to the ones used for propositional logic in the lectures

  - note: differently from lectures, where structural properties (of
    weakening, contraction, and exchange) were included as rules in
    their own right, in this project you will define a natural
    deduction proof system in which they are admissible

* Chapter 4 of The Proof Theory and Semantics of Intuitionistic Modal
  Logic (Simpson) (https://era.ed.ac.uk/handle/1842/407)

  - labelled natural deduction system for (intuitionistic) modal logic

  - note: this would be used if for some reason the Bierman-de Paiva
    style deduction system and its proof rules cause problems

### Temporal logic

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
