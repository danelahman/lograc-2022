# Reader, writer, and update monads

This file contains a single project.

## Source material

Based on the article:

  Update Monads: Cointerpreting Directed Containers
  by Ahman and Uustalu 
  ([link](https://drops.dagstuhl.de/opus/volltexte/2014/4623/))

## Goals of the project

* Formalise parts of the theory of reader, writer, and update monads:

  - definitions of reader, writer, state, and update monads by hand

  - examples of update monads

  - algebras of update monads (relating different presentations)

  - update monads as a compatible composition (via distributive law)
    of reader and writer monads, and that such distributive laws are
    in one-to-one correspondence with monoid actions

  - Maps of update monads

  - Update monads vs Kammar-Plotkin generlisation of state monads

* Parts of the formalisation that involve category theory should be
  formalised using
  [Agda's categories library](https://github.com/agda/agda-categories).
  This generalises from the lectures/exercises where for simplicity
  we were using shallow encodings of category-theoretic notions
  in Agda (e.g., object map of monad being of type `Set -> Set`).

  - for simplicity, you can work in the category of sets defined in
    `Categories.Category.Instance.Sets` in the categories library
