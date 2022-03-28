# Extension of PLFA

Extend the programming language formalised in Part 2 of the [PLFA
book](https://plfa.inf.ed.ac.uk) to include additional features.

* In detail, this means extracting the Agda code from the [literate
  Agda PLFA source files](https://github.com/plfa/plfa.github.io/tree/dev/src/plfa/part2), 
  extending the language with a given feature, and adapting and
  extending the subsequent definitions and proofs accordingly.

Some of the features you can extend Part 2 of PLFA with are:

* sums (they seem to be advertised in PLFA but not implemented)
    
  - see week 6 lecture recording for an overview of empty and sum types 
    in STLC, and together with the corresponding terms and equations
    
  - another thorough overview of sum types, their typing rules, and
    corresponding reduction rules can be found in Section 11.9 of
    Types and Programming Languages (Pierce)
    (https://www.cis.upenn.edu/~bcpierce/tapl/)

* lists (same as for sum types)

  - for lists, you should first look at how natural numbers are encoded 
    in PLFA, and then add lists based on the correspondence between 
    
    - (i) the `zero` constructor of natural numbers and the `[]`
      constructor of the list type, and

    - (ii) the `suc` constructor of naturla numbers and the `_∷_`
      constructor of the list type
      
  - an overview of another encoding of the list type, its typing
    rules, and corresponding reduction rules can be found in Section
    11.12 of Types and Programming Languages (Pierce)
    (https://www.cis.upenn.edu/~bcpierce/tapl/)

Further extensions:

* Moggi-style computational monad

  - an overview of monads, their use in modelling computational
    effects in lambda-calculi, and the corresponding programming
    abstractions can be found in Notions of Computation and Monads
    (Moggi) (https://www.cs.cmu.edu/~crary/819-f09/Moggi91.pdf)
