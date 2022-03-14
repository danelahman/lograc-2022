---------------------------------------------------------------------------
-- Week 4 exercises for the Logika v računalništvu course at UL FMF      --
-- Part 3 (Monads)                                                       --
--                                                                       --
-- Lecturer: Andrej Bauer                                                --
-- Teaching Assistant: Danel Ahman                                       --
--                                                                       --
-- Course website: https://ucilnica.fmf.uni-lj.si/course/view.php?id=252 --
-- Lecture notes: http://www.andrej.com/zapiski/ISRM-LOGRAC-2022/        --
---------------------------------------------------------------------------

{-
   This week's exercises are split between multiple modules.
   Solve them in the following order:

   1. `Dictionary.agda`
   2. `Monoid.agda`
   3. `Monad.agda`

   Attempt the bonus exercises only when you have finished all the
   numbered exercises.
-}

module Ex4.Monad where

open import Level        renaming (zero to lzero; suc to lsuc)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.List    using (List; []; _∷_; length)
open import Data.Maybe   using (Maybe; nothing; just)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s; _<_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_)
open import Data.Sum     using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit    using (⊤; tt)
open import Data.Vec     using (Vec; []; _∷_)

open import Function     using (id; _∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning      using (begin_; _≡⟨⟩_; step-≡; _∎)

{-
   Importing definitions of monoids from `Ex4.Monoid`.

   If you start working on this module before filling
   all the holes in `Ex4.Monoid`, please uncomment the
   pragma `{-# OPTIONS --allow-unsolved-metas #-}` in
   the beginning of the ``Ex4.Monoid` module.
-}

open import Ex4.Monoid


----------------
-- Exercise 5 --
----------------

{-
   Recall the record type of monads (in their Kleisli triple form).
-}

record Monad {l} : Set (lsuc l) where
  field
    -- carrier (object map) fo the Kleisli triple
    T       : Set l → Set l
    -- unit
    η       : {X : Set l} → X → T X
    -- bind
    _>>=_   : {X Y : Set l} → T X → (X → T Y) → T Y
    -- laws
    η-left  : {X Y : Set l} (x : X) (f : X → T Y) → η x >>= f ≡ f x
    η-right : {X : Set l} (c : T X) → c >>= η ≡ c
    >>=-assoc : {X Y Z : Set l} (c : T X) (f : X → T Y) (g : Y → T Z)
              → ((c >>= f) >>= g) ≡ c >>= (λ x → f x >>= g)

{-
   Show that any monoid induces a monad, namely, the writer monad.

   For background: In PL, the writer monad is used to model the
   computational effect of writing/outputting elements of a monoid.
-}

module _ {l} (Mon : Monoid {l}) where

  open Monoid Mon
  
  Writer : Monad {l}
  Writer = record {
    T         = λ X → M × X ;
    η         = {!!} ;
    _>>=_     = {!!} ;
    η-left    = {!!} ;
    η-right   = {!!} ;
    >>=-assoc = {!!} }


----------------
-- Exercise 6 --
----------------

{-
   Define an algebraic operation `write` for the `Writer` monad.
   Intuitively, given a monoid element `m`, `write` should model
   performing the computational effect of writing/outputting `m`.
-}

{-
   Notice the deliberate extra whitespace on the left to define
   `write` in the scope of the same anonymous module as `Writer`.
-}

  open Monad Writer

  write : {X : Set l} → T X → M → T X
  write k m' = {!!}

{-
   Prove that the `write` operation satisfies the equational theory
   corresponding to the writer monad.
-}

  write-ε : {X : Set l} → (k : T X) → write k ε ≡ k
        
  write-ε k = {!!}

  write-· : {X : Set l} → (k : T X) → (m m' : M)
          → write (write k m) m' ≡ write k (m · m')
 
  write-· k m' m'' = {!!}


----------------
-- Exercise 7 --
----------------

{-
   Show that every monad gives rise to a monoid. Notice that you
   have to define the monoid carrier type in the universe `Set₀`.

   Hint: The solution to this exercise is an instance of a well-known
   fact about the close relationship between monads and monoids.
-}

ToMonoid : (Mon : Monad {lzero}) → Monoid {lzero}
ToMonoid Mon = {!!}


--------------------------
-- Bonus Monad Exercise --
--------------------------

{-
   Construct a monad that combines the reader monad structure from the
   lecture and the writer monad structure we covered in these exercises.

   Given a type/set `S` and a monoid `(M,ε,·)`, the carrier of the
   respective monad is given by the functor `S → M × (-)`. Such monads
   are commonly called update monad update. For more information on them,
   see this article: https://danel.ahman.ee/papers/types13postproc.pdf.

   In order to equip the functor `S → M × (-)` with a monad structure, you
   will need additional (but standard) algebraic structure that describes
   the interaction of the type/set `S` and the monoid (`Act : ?` hole below).

   Can you reverse engineer this structure from what you need to define
   `>>=` and prove the monad laws? The name of the `Act` variable is a
   good hint, namely, you need an action of the monoid on `S`. Define
   this additional structure as a record type (data + equational laws).
-}

module _ {l} (S : Set l) (Mon : Monoid {l}) (Act : {!!}) where

  open Monoid Mon

  Update : Monad {l}
  Update = {!!}
