# Data structures & algorithms

This file describes 4 projects.

## Balanced search trees (3 projects)

Consider one variant of 
[self-balancing search trees](https://en.wikipedia.org/wiki/Self-balancing_binary_search_tree):

* [red-black tress](https://en.wikipedia.org/wiki/Red–black_tree)
* [2-3 trees](https://en.wikipedia.org/wiki/2–3_tree)
* [AVL trees](https://en.wikipedia.org/wiki/AVL_tree)

Your basic task is to formalise them *intrinsically*.

For a more advanced project, you can consider some of the following
extensions:

* implement dictionaries
* show that the trees are efficient (the depth is logarithmic)

## Priority queue (1 project)

The basic task is to give an *intrinsic* formalisation of 
[priority queues](https://en.wikipedia.org/wiki/Priority_queue), 
and to implement them in two ways: naively as lists, and as heaps.

For a more advanced project, you can implement queues using one of the
[specialised heaps](https://en.wikipedia.org/wiki/Priority_queue#Specialized_heaps).

## Effectful data structures in F*

The task is to learn how to use [F*](https://www.fstar-lang.org) and
implement effectful data structures. This project is suitable for
students who are willing to invest some time in learning a new tool,
and who already have some experience with proof assistants.

As an alternative, you could work on F* formalisation of something
else, such as low-level interrupt-driven embedded code or a low-level 
cryptographic protocol.

## Other suggested background reading materials

In addition to the wikipedia links above, a good general reference for
different kinds of data structures and algorithms on them is the book
"Introduction to Algorithms" by Cormen, Leiserson, Rivest, and Stein
(https://mitpress.mit.edu/books/introduction-algorithms-third-edition).

You can also look at Week 2 exercises to see one way how to
(extrinsically) specify a binary search tree in Agda. Note, however,
that in your projects you have to work with intrinsically specified
(suitable variant of) binary search trees.
