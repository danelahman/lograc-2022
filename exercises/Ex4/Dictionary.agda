---------------------------------------------------------------------------
-- Week 4 exercises for the Logika v računalništvu course at UL FMF      --
-- Part 1 (Dictionaries)                                                 --
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

module Ex4.Dictionary where

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

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {a b} → Extensionality a b


----------------
-- Exercise 1 --
----------------

{-
   Recall the record type of dictionary keys (supporting decidable
   equality) and the record type of dictionaries from the lecture.
-}

_≢_ : {l : Level} {A : Set l} → A → A → Set l
x ≢ y = x ≡ y → ⊥

data Dec {l : Level} (A : Set l) : Set l where
  yes : A → Dec A
  no  : (A → ⊥) → Dec A

record Key {l : Level} : Set (lsuc l) where
  field
    Keys      : Set l
    test-keys : (k k' : Keys) → Dec (k ≡ k')

record Dictionary {l₁ l₂ l₃ : Level}
                  (K : Key {l₁}) (A : Set l₂) : Set (lsuc (l₁ ⊔ l₂ ⊔ l₃)) where

  open Key K -- opening the `K` record to easily access its fields below
  
  field
    -- type of dictionary data (for storing key-value pairs)
    Dict      : Set l₃
    -- empty dictionary
    emp       : Dict
    -- look up a key in the dictionary
    lkp       : Dict → Keys → Maybe A
    -- add a key-value pair to the dictionary
    add       : Dict → Keys × A → Dict
    -- behavioural properties
    lkp-emp   : (k : Keys)
              → lkp emp k ≡ nothing
    lkp-add-≡ : (k : Keys) (x : A) (d : Dict)
              → lkp (add d (k , x)) k ≡ just x
    lkp-add-≢ : (k k' : Keys) (x : A) (d : Dict)
              → k ≢ k'
              → lkp (add d (k , x)) k' ≡ lkp d k'

  -- derived dictionary operation (add key-value pair only if key not present)
  add-if-new : Dict → Keys × A → Dict
  add-if-new d (k , x) with lkp d k
  ... | just _  = d
  ... | nothing = add d (k , x)

  {-
     Prove the following two properties about this derived
     operation using the properties of `lkp` and `add`.

     Hint: Using `rewrite` could be a good idea. Why so?
     Alternatively, you could use the `inspect` gadget:

       https://agda.readthedocs.io/en/v2.5.2/language/with-abstraction.html#the-inspect-idiom
  -}

  lkp-add-if-new-nothing : (k : Keys) (x : A) (d : Dict)
                         → lkp d k ≡ nothing
                         → lkp (add-if-new d (k , x)) k ≡ just x
                         
  lkp-add-if-new-nothing k x d p = {!!}

  lkp-add-if-new-just : (k : Keys) (x x' : A) (d : Dict)
                      → lkp d k ≡ just x'
                      → lkp (add-if-new d (k , x)) k ≡ just x'
                      
  lkp-add-if-new-just k x x' d p = {!!}


----------------
-- Exercise 2 --
----------------

{-
   Show that you can equip `List (K × A)` with a `Dictionary` structure.

   Note: We suggest you define `ListDict` using the `record { ... }`
   syntax instead of using copatterns. When writing out the sample
   solution to this exercise, we found that copatterns did not behave
   well when using `with` abstractions in the definitions. In
   addition, they also kept confusing Agda's termination checker.
-}

module _ {l₁ l₂} (K : Key {l₁}) (A : Set l₂) where

  open Key K
  open Dictionary

  ListDict : Dictionary K A
  ListDict = record {
    Dict      = List (Keys × A) ;
    emp       = {!!} ;
    lkp       = {!!} ;
    add       = {!!} ;
    lkp-emp   = {!!} ;
    lkp-add-≡ = {!!} ;
    lkp-add-≢ = {!!} }


----------------
-- Exercise 3 --
----------------

{-
   Here is a small refinement of the `Dictionary` record type with an
   extra behavioural property about `add` overwriting previous values.   
-}

record Dictionary' {l₁ l₂ l₃ : Level}
                   (K : Key {l₁}) (A : Set l₂) : Set (lsuc (l₁ ⊔ l₂ ⊔ l₃)) where

  open Key K

  field
    -- inheriting all the fields from a `Dictionary`
    Dict' : Dictionary {l₁} {l₂} {l₃} K A
  open Dictionary Dict'
  
  field
    -- an additional behavioural property
    add-add-≡ : (k : Keys) (x x' : A) (d : Dict)
              → add (add d (k , x)) (k , x') ≡ add d (k , x')

{-
   Show that the lists-based dictionaries also form a `Dictionary'`.

   Depending on whether you took any shortcuts when defining `add`
   above, you might need to redefine it to satisfy `add-add-≡`. If
   you need to redefine `add`, then you will likely also need to
   reprove the lemmas involved in defining `ListDict K A`.
-}

module _ {l₁ l₂} (K : Key {l₁}) (A : Set l₂) where

  open Key K
  open Dictionary'

  ListDict' : Dictionary' K A
  ListDict' = record {
    Dict'     = ListDict K A ;
    add-add-≡ = {!!} }


-------------------------------
-- Bonus Dictionary Exercise --
-------------------------------

{-
   Here is a further refinement of the `Dictionary` record type---this
   time it is refined with a further behavioural property `add-add-≢`,
   which states that `add` operations for distinct keys commute.
-}

record Dictionary'' {l₁ l₂ l₃ : Level}
                    (K : Key {l₁}) (A : Set l₂) : Set (lsuc (l₁ ⊔ l₂ ⊔ l₃)) where

  open Key K

  field
    Dict'' : Dictionary' {l₁} {l₂} {l₃} K A
  open Dictionary' Dict''
  open Dictionary  Dict'

  field
    -- a further behavioural property
    add-add-≢ : (k k' : Keys) (x x' : A) (d : Dict)
              → k ≢ k'
              → add (add d (k , x)) (k' , x') ≡ add (add d (k' , x')) (k , x)

{-
   Show that lists of key-value pairs can also be used to implement
   this dictionaries interface.

   Hint: You will likely need to refine the `Key` type with further
   order-theoretic properties to be able to define a new variant of
   the `add` operation that satisfies the `add-add-≢` property.
-}
