# Formalised mathematics

This file describes 5 projects, one per section.

## Algebras for a functor

This project requires learning the basics of category theory and using
[Agda's categories library](https://github.com/agda/agda-categories).

The basic task is to:

* define `F`-algebras and morphisms (alrady in the categories library)
* show that they form a category
* define polynomial functors on `Set` in one variable
* define initial `F`-algebras in terms of their universal property
* show that polynomial functors have initial algebras

Possible extensions:

* perform the construction more generally in a suitably nice category `𝒞`
* also define algebras for a monad, with examples

### Suggested background reading materials

* Chapter 10 of Category Theory (Awodey)
  (https://www.andrew.cmu.edu/course/80-413-713/notes/chap10.pdf)

  - Section 10.5 gives an overview of algebras for endofunctors,
    Lambek's lemma, polynomial functors and existence of their
    initial algebras

  - to show the existence of the initial algebras of polynomial
    functors, you can in first instance use the existence of
    initial algebras in Agda; and later show this existence
    also via the (co-)continuitiy of polynomial functors)

## Coalgebras for a functor

This project requires learning the basics of category theory and using
[Agda's categories library](https://github.com/agda/agda-categories).

The basic task is to:

* define `F`-coalgebras and morphisms (alrady in the categories library)
* show that they form a category
* define polynomial functors on `Set` in one variable
* define final `F`-coalgebras in terms of their universal property
* show that polynomial functors have final coalgebras

Possible extensions:

* perform the construction more generally in a suitably nice category `𝒞`
* also define coalgebras for a comonad, with examples


## Matrices

The basic objective is to define matrices over a commutative unital
ring `R`:

* define matrices as maps `Fin n × Fin m → R`
* define addition and multiplication of matrices
* show basic properties of addition and multiplication

Possible extensions:

* show equivalence of `m × n` matrices and the space `Vec n (Vec m)`
  from the exercises.
* define determinants and prove some of their properties


## Polynomials

The basic objective is to formalise polynomials over a commutative
unital ring `R` with *decidable equality*:

* the the type of polynomials `R[x]` in one variable
* prove that it forms an `R`-algebra
* define the degree of a polynomial and show its basic properties

Possible extensions:

* prove the universal property of `R[x]`
* show further properties of the polynomial ring


## Formal power series

The basic objective is to formalise 
[formal power series](https://en.wikipedia.org/wiki/Formal_power_series) 
over a field `F` with decidable equality:

* define the type of formal power series `F⟦x⟧` in one variable
* prove that it forms an `F`-algebra
* define [formal differentiation](https://en.wikipedia.org/wiki/Formal_power_series#Formal_differentiation) 
  and formalise its basic properties

Possible extensions:

* solve differential equations by solving recurrence relations

