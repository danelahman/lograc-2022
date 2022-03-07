---------------------------------------------------------------------------
-- Week 3 exercises for the Logika v računalništvu course at UL FMF      --
-- Lecturer: Andrej Bauer                                                --
-- Teaching Assistant: Danel Ahman                                       --
--                                                                       --
-- Course website: https://ucilnica.fmf.uni-lj.si/course/view.php?id=252 --
-- Lecture notes: http://www.andrej.com/zapiski/ISRM-LOGRAC-2022/        --
---------------------------------------------------------------------------

module Ex3 where

{-
   Imports from Agda's standard library. This is all you need to solve
   these exercises. If you need any auxiliary lemmas, prove them below.

   You can look up these imported definitions with the `M-.` command to.
-}

open import Data.Empty           using (⊥; ⊥-elim)
open import Data.Fin             using (Fin; zero; suc)
open import Data.List            using (List; []; _∷_; _++_; length; map)
open import Data.List.Properties using (map-id; map-compose)
open import Data.Maybe           using (Maybe; nothing; just)
open import Data.Nat             using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _<_)
open import Data.Nat.Properties  using (+-identityˡ; +-identityʳ; +-suc; +-comm)
open import Data.Product         using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_)
open import Data.Sum             using (_⊎_; inj₁; inj₂)
open import Data.Vec             using (Vec; []; _∷_)

open import Function             using (id; _∘_)

open import Relation.Nullary     using (¬_)

import Relation.Binary.PropositionalEquality as Eq
open Eq                          using (_≡_; refl; sym; trans; cong; subst)
open Eq.≡-Reasoning              using (begin_; _≡⟨⟩_; step-≡; _∎)

{-
   We also postulate the principle of function extensionality so
   that you can use it if and when needed in the exercises below.

   Recall that when spelled out in more detail, `fun-ext` has the type
   
   `fun-ext : {a b : Level} {A : Set a} {B : A → Set b} {f g : (x : A) → B x}
            → ((x : A) → f x ≡ g x)
            → f ≡ g`

   where `a` and `b` are universe levels (you can ignore them for time being).
-}

open import Axiom.Extensionality.Propositional using (Extensionality)

postulate fun-ext : ∀ {a b} → Extensionality a b


----------------
-- Exercise 1 --
----------------

{-
   Note: This exercise is brought over from week 2 exercise sheet.
   If you solved it last week, then just continue to next exercises. 
-}

{-
   Define a function that extracts the first `n` elements from a
   vector of length `n + m`, using recursion and pattern-matching.
-}

take-n : {A : Set} {n m : ℕ} → Vec A (n + m) → Vec A n
take-n xs = {!!}

{-
   Now define a function that extracts the first `n` elements from a
   vector of length `m + n` (notice the `m + n` vs `n + m` indices).

   Note: Do not define this function by recursion. Use the previously
   defined `take-n` and equational reasoning instead (hint: `subst`).
   
   Hint: The lemmas that we have imported from standard library's
   `Data.Nat.Properties` module could be useful for defining `take-n'`.
-}

take-n' : {A : Set} {n m : ℕ} → Vec A (m + n) → Vec A n
take-n' xs = {!!}


----------------
-- Exercise 2 --
----------------

{-
   Note: This exercise is brought over from week 2 exercise sheet.
   If you solved it last week, then just continue to next exercises. 
-}

{-
   Here are functions for translating vectors to lists and vice versa.
-}

vec-list : {A : Set} {n : ℕ} → Vec A n → List A
vec-list []       = []
vec-list (x ∷ xs) = x ∷ vec-list xs

list-vec : {A : Set} → (xs : List A) → Vec A (length xs)
list-vec []       = []
list-vec (x ∷ xs) = x ∷ list-vec xs

{-
   Prove that `vec-list` is a left inverse of `list-vec`.
   
   Hint: Observe that you have to prove equality between functions.
   For this you can use the postulated function extensionality axiom
   `fun-ext` (see the beginning of the file, under stdlib imports).
-}

list-vec-list : {A : Set}
              → vec-list ∘ list-vec ≡ id {A = List A}

list-vec-list = {!!}

{-
   Note: The dual lemma, showing that `list-vec` is the left inverse
   of `vec-list` is surprisingly involved---see last week's exercise
   sheet. Only attempt that if you have solved all other exercises.
-}


----------------
-- Exercise 3 --
----------------

{-
   Recall the partial lookup function from last week's exercises.
-}

lookup : {A : Set} {n : ℕ} → Vec A n → ℕ → Maybe A
lookup []       i       = nothing
lookup (x ∷ xs) zero    = just x
lookup (x ∷ xs) (suc i) = lookup xs i

{-
   Prove that this partial function is in fact total if the given index
   is in the range `{0,1,...,n-1}`.

   Last week we had this lemma restricted to vectors holding values of
   the unit type `T`. This week you are proving it for vectors holding
   values of an arbitrary type `A`. For this we use the `Σ`-type to
   state that there exists a value `x` that `lookup xs i` returns.
-}

lookup-total-Σ : {A : Set} {n : ℕ}
               → (xs : Vec A n)
               → (i : ℕ)
               → i < n
               → Σ[ x ∈ A ] (lookup xs i ≡ just x)

lookup-total-Σ xs i p = {!!}


----------------
-- Exercise 4 --
----------------

{-
   Next, we revisit another exercise from last week. This one was about
   translating a vector to a list.

   Differently from last week, we will use the `Σ`-type to encforce it in
   `vec-list-Σ`'s type that the returned list has the same length as the
   given vector. Recall that last week we were doing this extrinsically
   by proving an auxiliary equational lemma **after** defining `vec-list`.
-}

vec-list-Σ : {A : Set} {n : ℕ} → Vec A n → Σ[ xs ∈ List A ] (length xs ≡ n)
vec-list-Σ xs = {!!}


----------------
-- Exercise 5 --
----------------

{-
   Here's the safe lookup function for lists (in terms of the `<` relation).
-}

safe-list-lookup : {A : Set} → (xs : List A) → (i : ℕ) → i < length xs → A
safe-list-lookup (x ∷ xs) zero    (s≤s p) = x
safe-list-lookup (x ∷ xs) (suc i) (s≤s p) = safe-list-lookup xs i p

{-
   Establish the extensionality principle for lists: if two equal-length
   lists are index-wise equal, then these two lists are themselves equal.
-}

list-ext : {A : Set} {xs ys : List A}
         → length xs ≡ length ys
         → ((i : ℕ) → (p : i < length xs) → (q : i < length ys)
              → safe-list-lookup xs i p ≡ safe-list-lookup ys i q)
         → xs ≡ ys

list-ext = {!!}

{-
   Notice that we have generalised this statement a bit compared
   to what one would have likely written down in the first place.

   Namely, when comparing the values of the lists index-wise, we
   require separate proofs that `i < length xs` and `i < length ys`
   despite knowing that `length xs ≡ length ys`. We have done this
   to avoid having to use `subst` to fix the argument types in one
   of the applications of `safe-list-lookup`. If we would have used
   `subst` to fix the arguments, then we could have run into similar
   difficulties that we had with the last exercise on week 2 exercise
   sheet: having to additionally push `subst` through constructors.
-}


----------------
-- Exercise 6 --
----------------

{-
   Recall the record type of isomorphisms from the lecture.
-}

infix 0 _≃_

record _≃_ (A B : Set) : Set where         -- unicode `≃` with `\~-`
  field
    to      : A → B
    from    : B → A
    from∘to : (x : A) → from (to x) ≡ x
    to∘from : (y : B) → to (from y) ≡ y
    
open _≃_

{-
   Prove that the `Σ`-type is associative as a type former. For this, prove
   an isomorphism between the two different ways of associating `Σ`.
-}

{-
   First, prove this by constructing the isomorphism using the (old-school,
   functional programming style) `record { ... ; field = ... ; ... }` syntax.
-}

Σ-assoc : {A : Set} {B : A → Set} {C : (x : A) → B x → Set}
        → Σ[ x ∈ A ] (Σ[ y ∈ B x ] (C x y))
          ≃
          Σ[ xy ∈ Σ[ x ∈ A ] (B x) ] (C (proj₁ xy) (proj₂ xy))
        
Σ-assoc = {!!}

{-
   Second, prove the same thing using copatterns. For a reference on copatterns,
   see https://agda.readthedocs.io/en/v2.6.2.1/language/copatterns.html.
-}

Σ-assoc' : {A : Set} {B : A → Set} {C : (x : A) → B x → Set}
        → Σ[ x ∈ A ] (Σ[ y ∈ B x ] (C x y))
          ≃
          Σ[ xy ∈ Σ[ x ∈ A ] (B x) ] (C (proj₁ xy) (proj₂ xy))

Σ-assoc' = {!!}


----------------
-- Exercise 7 --
----------------

{-
   Prove that the `List` type former preserves isomorphisms.

   Hint: You might find it useful to use the `map` function on lists, 
   together with the lemmas we imported from `Data.List.Properties`.
-}

≃-List : {A B : Set} → A ≃ B → List A ≃ List B
≃-List = {!!}


----------------
-- Exercise 8 --
----------------

{-
   Recall the definition of types with decidable equality from lecture. 
-}

data Dec (A : Set) : Set where
  yes : A → Dec A
  no  : (A → ⊥) → Dec A

record DecSet : Set₁ where
  field
    DSet   : Set
    test-≡ : (x y : DSet) → Dec (x ≡ y)

open DecSet

{-
   Given a type with decidable equality, prove that a list holding
   elements of this type is itself a type with decidable equality.
-}

DecList : (DS : DecSet) → Σ[ DS' ∈ DecSet ] (DSet DS' ≡ List (DSet DS))
DecList DS = {!!}


----------------
-- Exercise 9 --
----------------

{-
   Recall the `add` function on lists from the end of last lecture.
-}

add : {DS : DecSet} → List (DSet DS) → DSet DS → List (DSet DS)
add [] x' = x' ∷ []
add {DS} (x ∷ xs) x' with (test-≡ DS) x x'
... | yes refl = x' ∷ xs
... | no  p    = x ∷ add {DS} xs x'

{-
   Recall that `add` was defined such that, intuitively, if given a
   list with no duplicates, then it returns a list with no duplicates.
   That's why we needed `DecSet` type and had to check whether `x ≡ x'`.

   Below we are going to make this intuitive correctness property of
   `add` formal by proving it in Agda.
-}

{-
   When thinking about how to specify that a given list has no duplicate
   elements, one likely first comes up with the `NoDup'` predicate below.
-}

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

safe-lookup : {A : Set} → (xs : List A) → Fin (length xs) → A
safe-lookup (x ∷ xs) zero    = x
safe-lookup (x ∷ xs) (suc n) = safe-lookup xs n

NoDup' : {A : Set} → List A → Set
NoDup' xs = (i j : Fin (length xs)) → i ≢ j → safe-lookup xs i ≢ safe-lookup xs j

{-
   While this is a mathematically and logically natural statement (any
   distinct pair of indices holds distinct values), it is not the best
   definition for proving theorems about it in type theory. Instead of
   characterising a negative statement (e.g., no duplicates) using a
   combination of function types/implications and negations, it is
   generally better if negative statements are also defined more
   "structurally"---as inductively defined predicates that then follow
   the structure of the type they are defined over (e.g., `List A`).

   (You can of course also try to prove `add-nodup` using `NoDup'`.)

   (As a bonus exercise, you can also try to separately prove that
   the `NoDup` and `NoDup'` predicates are logically equivalent.)
-}

{-
   So, instead, give below an inductive definition to the `NoDup` predicate.

   Hint: You might find the `∈` relation on lists defined below useful.
-}

infix 3 _∈_

data _∈_ {A : Set} : A → List A → Set where
  ∈-here  : {x : A} → {xs : List A} → x ∈ (x ∷ xs)
  ∈-there : {x y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

data NoDup {A : Set} : List A → Set where
  {- EXERCISE: replace this comment with constructors for `NoDup` -}

{-
   Next, prove some sanity-checks about the correctness of `NoDup`.
-}

nodup-test₁ : NoDup {ℕ} []
nodup-test₁ = {!!}

nodup-test₂ : NoDup (4 ∷ 2 ∷ [])
nodup-test₂ = {!!}

nodup-test₃ : ¬ (NoDup (4 ∷ 2 ∷ 4 ∷ []))
nodup-test₃ = {!!}

{-
   Finally, prove that `add` preserves the no-duplicates property.

   Hint: You might find it useful to prove an auxiliary lemma, showing
   that under certain conditions, if `x` is in `add xs x'`, then `x` was
   actually already present in `xs` (When would this be the case?).
-}

add-nodup : {DS : DecSet} → (xs : List (DSet DS)) → (x : DSet DS)
          → NoDup {DSet DS} xs
          → NoDup {DSet DS} (add {DS} xs x)

add-nodup xs x' p = {!!}


-----------------
-- Exercise 10 --
-----------------

{-
   Recall the type of binary numbers from week 1 exercises.
-}

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

infixl 20 _O
infixl 20 _I

{-
   Also recall the two translations of binary numbers into unary 
   numbers: one defined directly and the other defined in terms
   of an auxiliary function using an additional index argument.
-}

open import Data.Nat using (_*_; _^_)

from-bin : Bin → ℕ
from-bin ⟨⟩ = 0
from-bin (b O) = 2 * (from-bin b)
from-bin (b I) = 1 + 2 * (from-bin b)

private
  from-bin'-aux : Bin → ℕ → ℕ
  from-bin'-aux ⟨⟩    n = 0
  from-bin'-aux (b O) n = from-bin'-aux b (1 + n)
  from-bin'-aux (b I) n = 2 ^ n + from-bin'-aux b (1 + n)

from-bin' : Bin → ℕ
from-bin' b = from-bin'-aux b 0

{-
   Prove that these two translation functions are equal. Compared
   to the previous exercises, feel free to use any auxiliary lemmas
   about `ℕ`, `+`, `*`, and `^` that you can find in the standard
   library in the module `Data.Nat.Properties` imported below.

   You can find a web-browsable version of this library module at

     https://agda.github.io/agda-stdlib/Data.Nat.Properties.html

   Hint: Similarly to the list reversal function in the lecture, you
   will need to generalise the statement `from-bin b ≡ from-bin' b`
   and come up with a loop invariant for the function `from-bin'-aux`.
-}

open import Data.Nat.Properties

from-bin-≡ : (b : Bin) → from-bin b ≡ from-bin' b
from-bin-≡ b = {!!}
