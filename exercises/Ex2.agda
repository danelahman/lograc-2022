---------------------------------------------------------------------------
-- Week 2 exercises for the Logika v računalništvu course at UL FMF      --
-- Lecturer: Andrej Bauer                                                --
-- Teaching Assistant: Danel Ahman                                       --
--                                                                       --
-- Course website: https://ucilnica.fmf.uni-lj.si/course/view.php?id=252 --
-- Lecture notes: http://www.andrej.com/zapiski/ISRM-LOGRAC-2022/        --
---------------------------------------------------------------------------

module Ex2 where

{-
   ACTION ITEM 1: There are many exercises on this week's exercise sheet.
   
   To make tackling them easier, we have divided them into three
   groups: (i) simpler, (ii) more involved, and (iii) most involved.

   You should definitely solve the exercises in the simpler group, and
   then attempt the exercises in the other groups for more of a
   challenge (the last group is roughly at the level you could expect
   to have to cope with in your project work if aming for top marks).
-}

{-
   ACTION ITEM 2: First time loading this file will take a bit of time
   because Agda will typecheck all the standard library dependencies
   you have not used before. You should see the progress of this in the
   buffer/window below this one. If you get errors related to Agda not
   finding the `Data.Nat` module (or others similar), then you most
   likely do not have the standard library set up correctly. See the
   README.md file for help on how to set up the standard library.
-}

{-
   ACTION ITEM 3: Those of you using VS Code and the experimental Agda
   Language Server provided by the agda-mode extension might see weird
   behaviour with the file loading taking very long time and/or it not
   getting properly highlighted. If this happens, use the block comments
   `{- ... -}` to comment out the solutions you have not yet attempted
   to solve. Having fewer unfilled holes seems to help with this problem.
-}

{-
   This week we are also starting to use the standard library. We
   will not be defining natural numbers, lists, etc from scratch any
   more by hand---instead we import them from the standard library.

   In your solutions do not use anything more from the standard
   library than listed in the `using` blocks below. Any additional
   required lemmas should be proved (for educational purposes) as part
   of your solutions, but of course in your future project work you
   should be reusing as much as possible from the standard library.
-}

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; length)
open import Function using (id; _∘_)

{-
   We are also importing the equality type and the corresponding
   equational reasoning machinery from the standard library. See
   this week's lecture for more info about equational reasoning.
-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst; resp)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Axiom.Extensionality.Propositional using (Extensionality)

{-
   We also postulate the principle of function extensionality so
   that you can use it if and when needed in the exercises below.

   Recall that when spelled out in more detail, `fun-ext` has the type
   
   `fun-ext : {a b : Level} {A : Set a} {B : A → Set b} {f g : (x : A) → B x}
            → ((x : A) → f x ≡ g x)
            → f ≡ g`

   where `a` and `b` are universe levels (as mentioned in lecture 1).
-}

postulate
  fun-ext : ∀ {a b} → Extensionality a b


-------------------------------
-------------------------------
-- SIMPLER EXERCISES [START] --
-------------------------------
-------------------------------

----------------
-- Exercise 0 --
----------------

{-
   Start by proving the following simple equational properties about
   natural numbers and addition. Hint: Use induction. You might find
   it useful to recall the congruence principle `cong` from lecture.
-}

+-identityʳ : (n : ℕ) → n + zero ≡ n
+-identityʳ n = {!!}

+-identityˡ : (n : ℕ) → zero + n ≡ n
+-identityˡ n = {!!}

+-suc : (n m : ℕ) → n + (suc m) ≡ suc (n + m)
+-suc n m = {!!}


----------------
-- Exercise 1 --
----------------

{-
   Next, recall the type of vectors from the lecture.
-}

infixr 5 _∷_

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : {n : ℕ} → (x : A) → (xs : Vec A n) → Vec A (suc n)

{-
   Define the function `lookup` that looks up the value in a given
   vector at a given natural number index.

   As the index below can be an arbitrary natural number, then we have
   to define `lookup` as a partial function. We do this by giving
   `lookup` the `Maybe` return type, which has two constructors:
   one for the value if the function is defined, and one to mark that
   that the functions is not defined. Set-theoretically, `Maybe A`
   should be read as the disjoint union of sets `A` and `{ nothing }`.
-}

data Maybe (A : Set) : Set where
  just    : A → Maybe A
  nothing : Maybe A

lookup : {A : Set} {n : ℕ} → Vec A n → ℕ → Maybe A
lookup xs i = {!!}


----------------
-- Exercise 2 --
----------------

{-
   Prove that the above partial `lookup` function is total if the index
   to be looked up is from the finite set `{ 0 , 1 , ... , n - 1 }`. We
   formalise this last part by including a proof argument witnessing that
   the given index `i` satisfies the relation `i < n`, which we derive
   from the "less than or equal" relation `≤` that you saw last week.

   For simplicity, we will specialise the lemma to vectors containing
   unit-typed values (`⊤` has a unique inhabitant `⋆`). After being
   introduced to means for existentially quantifying values in types
   next week, you will be able to generalise this to arbitrary types.
-}

_<_ : ℕ → ℕ → Set
n < m = suc n ≤ m

_>_ : ℕ → ℕ → Set
n > m = m < n

infix 4 _<_
infix 4 _>_

data ⊤ : Set where
  ⋆ : ⊤                                         -- `⋆` typed as `\*`

lookup-totalᵀ : {n : ℕ}
              → (xs : Vec ⊤ n)
              → (i : ℕ)
              → i < n                           -- `i` in `{0,1,...,n-1}`
              → lookup xs i ≡ just ⋆
             
lookup-totalᵀ xs i p = {!!}

{-
   Note: In the standard library, `⊤` is defined as a record type. Here
   we defined it temporarily as an inductive type because you have not
   yet learned about record types in Agda.
-}


----------------
-- Exercise 3 --
----------------

{-
   The `lookup-totalᵀ` lemma above is commonly called an "extrinsic"
   proof because we prove the correctness of `lookup` after the fact,
   externally to its (simply typed, regarding the index `i`) definition.

   In contrast, we could instead make use of the expressiveness of
   dependent types and define an alternative `safe-lookup` function
   that is total and guaranteed to always return a value of type `A`.
   In this case one will have to prove that the index is in the range
   in order to be able to call the `safe-lookup` function below.

   We do this by restricting the index argument of the function to be
   from the finite set of natural numbers `{ 0 , 1 , ... , n - 1 }`
   already in the type signature of the lookup function. For this we
   will use the dependent type `Fin` defined below. As this "correctness
   of the index argument" specification is now imposed in the types at
   definition time, this style of proof is commonly called "intrinsic".

   Intuitively, `Fin n` is the finite set `{ 0 , 1 , ... , n - 1 }`.
-}

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} (i : Fin n) → Fin (suc n)

safe-lookup : {A : Set} {n : ℕ} → Vec A n → Fin n → A
safe-lookup xs i = {!!}


----------------
-- Exercise 4 --
----------------

{-
   Prove that the two lookup functions compute the same value if the
   given index is in an appropriate range.

   In order to pass the given natural number `i` as an argument to the
   `safe-lookup` function, you will have to convert it to an element
   of `Fin` with the `nat-to-fin` function. As a challenge, the type
   of `nat-to-fin` is left for you to complete (notice the hole in the
   type). Hint: You should be able to reverse-engineer it from its use
   in the type of `lookup-correct` below. If you fill the hole with
   the correct type, the yellow highlighting below will disappear.
-}

nat-to-fin : {!!}
nat-to-fin = {!!}

lookup-correct : {A : Set} {n : ℕ}
               → (xs : Vec A n)
               → (i : ℕ)
               → (p : i < n)
               → lookup xs i ≡ just (safe-lookup xs (nat-to-fin i p))

lookup-correct x i p = {!!}


----------------
-- Exercise 5 --
----------------

{-
   Define a function that extracts the first `n` elements from a
   vector of length `n + m`.
-}

take-n : {A : Set} {n m : ℕ} → Vec A (n + m) → Vec A n
take-n xs = {!!}


----------------
-- Exercise 6 --
----------------

{-
   Define a function that extracts the first `n` elements from
   a vector of length `m + n`. Hint: Do not define this function
   by recursion. Use `take-n` and equational reasoning instead.
-}

take-n' : {A : Set} {n m : ℕ} → Vec A (m + n) → Vec A n
take-n' xs = {!!}


----------------
-- Exercise 7 --
----------------

{-
   Define a function from vectors to lists that is identity on the
   list elements but forgets the length-index of the vector type.
-}

vec-list : {A : Set} {n : ℕ} → Vec A n → List A
vec-list xs = {!!}

{-
   Define a function from lists to vectors that is identity on the
   elements.

   Note the hole in the result type. Fill it with an appropriate 
   natural number specifying the length of the returned vector.
-}

list-vec : {A : Set} → (xs : List A) → Vec A {!!}
list-vec xs = {!!}


----------------
-- Exercise 8 --
----------------

{-
   Prove that the `vec-list` function produces a list with the same
   length as the given vector.
-}

vec-list-length : {A : Set} {n : ℕ}
                → (xs : Vec A n)
                → n ≡ length (vec-list xs)
                
vec-list-length xs = {!!}


----------------
-- Exercise 9 --
----------------

{-
   For mathematics, the `Vec` type is also useful for representing
   dimension-safe matrices and operations on them in Agda. In detail,
   we define a dimension-safe m by n matrix as a length-m vector
   (modelling the rows) of length-n vectors (modelling the columns).
-}

Matrix : Set → ℕ → ℕ → Set
Matrix A m n = Vec (Vec A n) m

{-
   Define the addition of two matrices holding natural-number values.

   Observe that because we have used dependent types to define the
   type of matrices, then we will not have to worry about mismatches
   of the numbers of rows or columns in the definition (contrast this
   to how you would define matrix addition in a simply typed language).

   Hint: You might find it helpful to define the point-wise addition
   of two vectors of the same length.
-}

_+ᴹ_ : {m n : ℕ} → Matrix ℕ m n → Matrix ℕ m n → Matrix ℕ m n
xss +ᴹ yss = {!!}


-----------------------------
-----------------------------
-- SIMPLER EXERCISES [END] --
-----------------------------
-----------------------------


-------------------------------------
-------------------------------------
-- MORE INVOLVED EXERCISES [START] --
-------------------------------------
-------------------------------------

-----------------
-- Exercise 10 --
-----------------

{-
   Prove that `vec-list` is the left inverse of `list-vec`.
   Observe that you have to prove equality between functions.
-}

list-vec-list : {A : Set}
              → vec-list ∘ list-vec ≡ id {A = List A}
              
list-vec-list = {!!}


-----------------
-- Exercise 11 --
-----------------

{-
   Define the transpose of a matrix.

   Hint 1: You might find it helpful to define an auxiliary function
   function to populate a length-n vector with a given value `x`.

   Hint 2: When defining `transpose`, think how you would express it
   in terms of the transpose of the submatrix without the first row.
-}

transpose : {A : Set} {m n : ℕ} → Matrix A m n → Matrix A n m
transpose xss = {!!}


-----------------
-- Exercise 12 --
-----------------

{-
   Below we shall be working with sorted trees holding natural numbers,
   variations of which occur commonly in computer science applications.

   When defining operations on such trees (e.g., inserting an element
   into a tree), it will be useful to be able to test whether two
   natural numbers are equal or related by the `<` or `>` relations.
   Below we give an inductively defined relation that witnesses which
   of these three situations holds of a given two natural numbers.

   This is an instance of a more general phenomena of decidability
   and reflection in type theory. For more information, see the Decidable
   section in the PLFA textbook (https://plfa.inf.ed.ac.uk/Decidable/).
-}

data _</≡/>_ (n m : ℕ) : Set where
  n<m : n < m → n </≡/> m
  n≡m : n ≡ m → n </≡/> m
  n>m : n > m → n </≡/> m

{-
   Define a function `test-</≡/>` that, given two natural numbers,
   returns the proof of either `n < m`, `n ≡ m`, or `n > m`
   depending on the relationship between the given two numbers.

   In its essence, the function `test-</≡/>` shows that the natural
   ordering relation on natural numbers is total and decidable---we
   can compute which of the three situations actually holds. See
   PLFA (https://plfa.inf.ed.ac.uk/Decidable/) for more details.
-}

test-</≡/> : (n m : ℕ) → n </≡/> m
test-</≡/> n m = {!!}


-----------------
-- Exercise 13 --
-----------------

{-
   Below is the inductive type `Tree A` of node-labelled binary trees
   holding data of type `A` in their nodes. Such a tree is either an
   `empty` tree (holding no data); or a root node built from a left
   subtree `t`, data `n`, and a right subtree `u`, written `node t n u`.

   For example, the binary tree

           42
           /\
          /  \
         22  52
          \
           \
           32

   would be represented in Agda as the expression

     `node (node empty 22 (node empty 32 empty)) 42 (node empty 52 empty)`

   of type `Tree ℕ`.
-}

data Tree (A : Set) : Set where
  empty : Tree A
  node  : Tree A → A → Tree A → Tree A

{-
   For trees holding natural numbers, define a function that inserts a
   given natural number into a tree following the insertion strategy for
   binary search trees (https://en.wikipedia.org/wiki/Binary_search_tree).

   Namely, when inserting a number `n` into an `empty` tree, the function
   should create a new trivial tree containing just `n`; and when recursively
   inserting a number `n` into a tree of the form `node t m u`, the function
   should behave as one of the following three cases:
   - if n = m, then the function just returns the given tree, doing nothing;
   - if n < m, then the function recursively tries to add `n` into `t`; or
   - if n > m, then the function recursively tries to add `n` into `u`.

   Hint: When testing which of the three situations holds for a `node t m u`
   case, you might find it helpful to use Agda's `with` abstraction
   (https://agda.readthedocs.io/en/v2.6.2.1/language/with-abstraction.html)
   to do perform pattern-matching without having to define auxiliary functions.
-}

insert : Tree ℕ → ℕ → Tree ℕ
insert t n = {!!}

{-
   As a sanity check, prove that inserting 12, 27, and 52 into the above
   example tree correctly returns the expected trees.
-}

insert-12 : insert (node (node empty 22 (node empty 32 empty)) 42 (node empty 52 empty)) 12
            ≡
            node (node (node empty 12 empty) 22 (node empty 32 empty)) 42 (node empty 52 empty)
insert-12 = {!!}

insert-27 : insert (node (node empty 22 (node empty 32 empty)) 42 (node empty 52 empty)) 27
            ≡
            node (node empty 22 (node (node empty 27 empty) 32 empty)) 42 (node empty 52 empty)
insert-27 = {!!}            

insert-52 : insert (node (node empty 22 (node empty 32 empty)) 42 (node empty 52 empty)) 52
            ≡
            node (node empty 22 (node empty 32 empty)) 42 (node empty 52 empty)
insert-52 = {!!}


-----------------
-- Exercise 14 --
-----------------

{-
   Define an inductive relation `∈` that specifies that a given natural
   number exists in the given tree.

   Hint: This relation should specify a path in a given tree from its
   root to the desired natural number whose existence we are specifying.
-}

data _∈_ (n : ℕ) : Tree ℕ → Set where
  {- EXERCISE: the constructors for the `∈` relation go here -}


{-
   Prove that the tree returned by the `insert` function indeed
   contains the inserted natural number.

   Hint: If you used Agda's `with` abstraction for pattern-matching in
   the definition of `insert`, you will need to perform similar amount
   of pattern-matching also in this proof to make the type of the hole
   compute. You can tell when this is needed because the type of the
   hole will involve an expression of the form `f v | g w`, meaning
   that in order for `f v` to be computed and normalised further, you
   need to first pattern-match on the value of `g v` (using `with`).

   If you haven't spotted this already, then it is part of a general
   pattern---proofs often follow the same structure as the definitions.
-}

insert-∈ : (t : Tree ℕ) → (n : ℕ) → n ∈ (insert t n)
insert-∈ t n = {!!}


-----------------------------------
-----------------------------------
-- MORE INVOLVED EXERCISES [END] --
-----------------------------------
-----------------------------------


-------------------------------------
-------------------------------------
-- MOST INVOLVED EXERCISES [START] --
-------------------------------------
-------------------------------------

-----------------
-- Exercise 15 --
-----------------

{-
   While above you were asked to define the `insert` function
   following the insertion strategy for binary search trees, then
   concretely the function is still working on arbitrary binary
   trees. Here we will define an inductive predicate to classify
   binary trees that are indeed binary search trees and prove that
   the `insert` function preserves this predicate.
-}

{-
   Before we define the binary search tree predicate, we extend
   the type of natural numbers with bottom and top elements,
   written `-∞` and `+∞` (for symmetry and their analogy with
   negative and positive infinities; also, `⊥` and `⊤` are already
   used in Agda for the empty and unit type). We then also extend the
   order `<` to take these new bottom and top elements into account.
-}

data ℕ∞ : Set where
  -∞  :     ℕ∞
  [_] : ℕ → ℕ∞
  +∞  :     ℕ∞

data _<∞_ : ℕ∞ → ℕ∞ → Set where
  -∞<n  : {n   : ℕ∞}  →          -∞   <∞   n
  []<[] : {n m : ℕ}   → n < m → [ n ] <∞ [ m ]
  n<+∞  : {n   : ℕ∞}  →           n   <∞  +∞

{-
   Using this extended definition of natural numbers, we next define
   an inductive predicate `IsBST` on binary trees that specifies when
   a given binary tree holding natural numbers is in fact a binary
   search tree (https://en.wikipedia.org/wiki/Binary_search_tree).

   Note that, concretely, the `IsBST` predicate consists of two definitions:
   - the `IsBST` predicate, which is the "top-level" predicate specifying
     that a given binary tree is in a binary search tree format; and
   - the recursively defined relation `IsBST-rec`, which does most of the
     work in imposing the binary search tree invariant on the given tree.

   The `IsBST-rec` relation carries two additional `ℕ∞`-arguments that
   specify the range of values a given binary search tree is allowed
   to hold, in particular, which values the left and right subtrees of
   a `node t n u` tree node are allowed to store. Further, note that the
   `empty` case holds a proof that `lower` is indeed less than `upper`.   
-}

data IsBST-rec (lower upper : ℕ∞) : Tree ℕ → Set where
  empty-bst : (p : lower <∞ upper) → IsBST-rec lower upper empty
  node-bst  : {t u : Tree ℕ} {n : ℕ}
            → IsBST-rec lower [ n ] t
            → IsBST-rec [ n ] upper u
            → IsBST-rec lower upper (node t n u)

data IsBST : Tree ℕ → Set where
  empty-bst : IsBST empty
  node-bst  : {t u : Tree ℕ} {n : ℕ}
            → IsBST-rec -∞ [ n ] t
            → IsBST-rec [ n ] +∞ u
            → IsBST (node t n u)

{-
   Prove that having the `(p : lower <∞ upper)` proof witness in the
   `empty` cases of the `IsBST-rec` relation indeed forces the `<∞`
   relation to hold for the bound indices of `IsBST-rec` in general.

   Hint: You might find it helpful to prove the transitivity of `<∞`.
-}

isbst-rec-<∞ : {lower upper : ℕ∞} {t : Tree ℕ}
             → IsBST-rec lower upper t
             → lower <∞ upper
             
isbst-rec-<∞ p = {!!}

{-
   Disclaimer: The `(p : lower <∞ upper)` proof witness in the `empty`
   case of the `IsBST-rec` relation means that every proof about a
   given tree being a binary search tree needs one to construct such
   proofs explicitly for all `empty` (sub)trees. For example, see below:
-}

bst : IsBST (node (node empty 2 (node empty 3 empty)) 5 (node empty 6 empty))
bst = node-bst
        (node-bst
           (empty-bst -∞<n)
           (node-bst
              (empty-bst ([]<[] (s≤s (s≤s (s≤s z≤n)))))
              (empty-bst ([]<[] (s≤s (s≤s (s≤s (s≤s z≤n))))))))
        (node-bst
           (empty-bst ([]<[] (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
           (empty-bst n<+∞))

{-
   A more user-friendly variant of the `IsBST-rec` relation could use
   Agda's instance arguments `{{...}}` and type classes to attempt to
   automatically fill in such proof witnesses as much as possible.
   
   You don't need to switch to instance arguments here, but they could
   be useful in your project work. For more information about them, see
   https://agda.readthedocs.io/en/v2.6.2.1/language/instance-arguments.html.
   Instance arguments and type classes will also be covered in lectures.

   Note: Other proof assistants can have different ways how to fill
   such proof witnesses in automatically, ranging from tactics and
   meta-programming to refinement types and SMT-based automation.
-}


-----------------
-- Exercise 16 --
-----------------

{-
   Prove that being a binary search tree is invariant under `insert`.

   Hint: As the `IsBST` predicate is defined in two steps, then you
   might find it useful to prove an auxiliary lemma about `insert`
   preserving also the recursively defined `IsBST-rec` relation.
-}

insert-bst : (t : Tree ℕ) → (n : ℕ) → IsBST t → IsBST (insert t n)
insert-bst t n p = {!!}


-----------------
-- Exercise 17 --
-----------------

{-
   Prove that `list-vec` is the left inverse of `vec-list`.
   Observe that you have to prove equality between functions.

   Note that if we simply wrote `id` as the right-hand side of the
   equational property below we would get a typing error about a
   mismatch in the natural number indices. Find a way to fix the type
   of a given vector to use it in the right-hand side of the equation.

   Hint 1: For a slightly unsatisfactory solution, think how you could
   convert a given vector to another of a given type using recursion.

   Hint 2: For a more complete solution, recall from the lecture how
   one change the type of a given value (e.g., a vector) using a
   previously proved equality proof, and then combine this with one of
   the equational lemmas we proved above.

   WARNING: The hint 2 solution of this exercise is probably the most
   complex on this exercise sheet, as it will require some careful
   thought when generalising the concrete statement you are trying to
   prove, relating element-wise equality of vectors to the `≡` relation
   on vectors, etc. So we suggest you leave this one for the very last.
-}

vec-list-vec : {A : Set} {n : ℕ}
             → list-vec ∘ vec-list ≡ {!!}
               
vec-list-vec = {!!}


-----------------------------------
-----------------------------------
-- MOST INVOLVED EXERCISES [END] --
-----------------------------------
-----------------------------------

