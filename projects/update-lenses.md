# Ordinary and update lenses

This file contains a single project.

## Source material

Based on the article:

  Coalgebraic Update Lenses
  by Ahman and Uustalu 
  ([link](https://www.sciencedirect.com/science/article/pii/S157106611400070X?via%3Dihub))

## Goals of the project

* Formalise parts of the theory of ordinary and update lenses:

  - definitions of ordinary and update lenses by hand (as (co-)algebraic
    structures, given by (co-)operations and (co-)equations)

  - examples of ordinary and update lenses 

* Formalise and relate alternative characterisations of ordinary and
  update lenses:

  - for ordinary lenses: as algebras of a monad on slice category, as
    coalgebras for the costate/array comonad
  
  - for update lenses: bialgebras of a functor and monad, bialgebras
     of a comonad and monad, pairs of coalgebras of two comonads,
     coalgebras of a comonad
     
  - functor from ordinary lenses to update lenses

* Parts of the formalisation that involve category theory should be
  formalised using
  [Agda's categories library](https://github.com/agda/agda-categories):

  - for simplicity, you can work in the category of sets defined in
    `Categories.Category.Instance.Sets` in the categories library
