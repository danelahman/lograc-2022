# Hoare logics for WHILE (and STLC)

This file contains 3 projects, depending on which feature X you choose.

## Source material

A good general reference for different kinds of logics (including
Hoare Logic) is the book "Logic in Computer Science" by Huth & Ryan
([link](https://www.cs.bham.ac.uk/research/projects/lics/)).

  - as a warm-up exercise, you should take the propositional logic and 
    its semantics from the exercise classes, and change the semantics
    to be valued in `HProp` instead if `Bool` (see week 6 lecture notes
    and [HProp.agda](agda/HProp.agda) for explanation of `HProp`)

## Goals of the project

* Define a deep embedding of a small imperative programming language
  (commonly called the WHILE language) extended with feature(s) X.

  - As discussed in Huth & Ryan, you should have three syntactic classes
    of terms:
    
    - integer expressions `E ::= i | l | (-E) | E + E' | ...`

    - boolean expressions `B ::= true | false | (!B) | ... | E < E'`
    
    - computations `C ::= skip | l = E | C;C | ...`
    
    - where `i` ranges over integer constants and `l` ranges over
      some fixed type/set of locations (likely need decidable equality
      for them as well)

  - In the first instance, instead of the general (possibly) divergent
    while loop construct `WHILE B DO C`, use a terminating for loop
    combinator `FOR E1 to E2 do C` (where you give the lower and upper
    bounds for the loop index, which is then incremented implicitly).

  - Once you have everything working for the terminating variant of
    WHILE (including the bullet points below), then an additional
    challenge is to use the delay monad to allow possibly divergent
    computations (like the general while loop construct).

* Features X you can choose from (you can of course suggest your own):

  1. state and exceptions
  
     - assume a type/set of exceptions `Exc` (likely needs decidable `≡`)
  
     - for this, you need to extend WHILE with further operations for
       raising exceptions `raise e` (where `e` is an exception name) and
       for catching exceptions `try C with (raise e -> C_e)_{e in Exc}`.
  
  2. state and input/output
  
     - for simplicity, input/output only for boolean values
  
     - for this, you need to extend WHILE with further operations for
       reading from (standard) input `read C_true C_false` and for
       writing to (standard) output `write_true C` and `write_false C`
  
  3. state and nondeterminism

     - for this, you need to extend WHILE with further operation for
       making a nondeterministic choice `C or C'`

* Define a definitional interpreter for WHILE + X.

  - This means defining an interpretation `[[_]] : Commands -> T 1`,
    where `T` is a monad corresponding to the feature X you chose:

    1. For state and exceptions, `T X = State -> (X x State) + Exc`
       where `Exc` is some assumed type/set of exception names.
       
       This is the so-called "state with rollback" combination of
       state and exceptions, where the state is discarded when an 
       exception occurs (and it is rolled back to the initial state
       when handling such an exception).

    2. For state and IO, `T X = State -> IO (X x State)`, where `IO`
       is the input/output monad, i.e., computation trees built from 
       input `read` and output `write_true, write_false` operations.
       
    3. For state and nondeterminism, `T X = State -> List (X x State)`, 
       where the `List` monad is used to model nondeterministic results.
       
       As an extension / bonus, you can later try to define and use a 
       finite powerset monad instead of `List` to validate further laws
       of nondeterministic computations (idempotency and symmetry).
    
    In the above, the state space is defined as `State = Location -> Int`.

* Define a deep embedding of Hoare Logic for WHILE + X.
    
  - For the logic of stateful pre- and postconditions, I recommend that you
    use propositional logic extended with (in)equality between the integer
    valued expressions, i.e., `phi, psi ::= ... | E_1 = E_2 | E_1 < E_2`.
    You will then also need to extend the proof system for propositional
    logic from exercises accordingly.
    
  - If working on (1), then you also need another class of formulae 
    `epsilon ::= e | epsilon \/ epsilon'`, such that the preconditions 
    of the Hoare triples are stateful formulae `phi` and the postconditions
    are the disjoint union of `phi` and `epsilon` formulae.
    
  - If working on (2), then the preconditions of the Hoare triples would
    be stateful formulae `phi` and the postconditions would be pairs of
    a stateful formula `phi` and a formula specifying a sequence of 
    input-output events
    
  - If working on (3), then both the pre- and postconditions would be 
    stateful formulae `phi`. However, in this case, you need to define
    two Hoare Logics, one for angelic (at least one of the final results
    must make the postcondition true) and one for demonic nondeterminism
    (all the final results need to make the postcondition true).

* Prove that the Hoare Logic is sound with respect to the definitional
  interpreter in the partial correctness reading:
  
  - This means that given a Hoare triple `{P} C {Q}`, then for all states, 
    if the state satisfies the precondition, and `C` terminates when run
    on this state, then the final state satisfies `Q`. That exactly 
    terminates and satisfies means here depends on the X you chose above.

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

### Delay monad

* Section 3 of The Delay Monad and Restriction Categories (Uustalu,
  Veltri) (https://pure.itu.dk/ws/files/82292987/ictac17_revised.pdf)

  - an overview of the delay monad (as a coinductive data type)

* Coinduction section of Agda User Manual
  (https://agda.readthedocs.io/en/v2.6.2.1/language/coinduction.html)

  - demonstrates how to define and work with infinite, coinductively
    defined data types in Agda (of which the delay monad is an example)
