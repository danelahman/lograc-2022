------------------------------------------------------------------------------------
-- Solutions to Week 4 exercises for the Logika v računalništvu course at UL FMF  --
-- Part 1 (Dictionaries)                                                          --
--                                                                                --
-- Lecturer: Andrej Bauer                                                         --
-- Teaching Assistant: Danel Ahman                                                --
--                                                                                --
-- Course website: https://ucilnica.fmf.uni-lj.si/course/view.php?id=252          --
-- Lecture notes: http://www.andrej.com/zapiski/ISRM-LOGRAC-2022/                 --
------------------------------------------------------------------------------------

module Sol4.Dictionary where

open import Level        renaming (zero to lzero; suc to lsuc)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.List    using (List; []; _∷_; length)
open import Data.Maybe   using (Maybe; nothing; just)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s; _<_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_; curry; uncurry)
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

  {-
     This reflexivity property (`test-keys-refl`) of key equality
     testing is needed quite often in the exercises below. Therefore,
     we prove it as a derived lemma within the `Key` record type.
  -}

  test-keys-refl : (k : Keys) → test-keys k k ≡ yes refl
  test-keys-refl k with test-keys k k
  ... | yes refl = refl
  ... | no  p    = ⊥-elim (p refl)

  {-
     And here are two additional derived lemmas about `test-keys`.
  -}

  test-keys-≡ : (k k' : Keys) → (p : k ≡ k') → test-keys k k' ≡ yes p
  test-keys-≡ k .k refl = test-keys-refl k

  test-keys-≢ : (k k' : Keys) → (p : k ≢ k') → test-keys k k' ≡ no p
  test-keys-≢ k k' p with test-keys k k'
  ... | yes refl = ⊥-elim (p refl)
  ... | no  q    = cong no (fun-ext (λ r → ⊥-elim (p r)))


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
                         
  lkp-add-if-new-nothing k x d p rewrite p = lkp-add-≡ k x d

  ---

  lkp-add-if-new-just : (k : Keys) (x x' : A) (d : Dict)
                      → lkp d k ≡ just x'
                      → lkp (add-if-new d (k , x)) k ≡ just x'
                      
  lkp-add-if-new-just k x x' d p rewrite p = p

  {-
     And the proof of the second property using `inspect`.
  -}

  lkp-add-if-new-just' : (k : Keys) (x x' : A) (d : Dict)
                       → lkp d k ≡ just x'
                       → lkp (add-if-new d (k , x)) k ≡ just x'
                       
  lkp-add-if-new-just' k x x' d p with lkp d k | inspect (uncurry lkp) (d , k)
  ... | just x'' | [ eq ] =
    begin
      lkp d k
    ≡⟨ eq ⟩
      just x''
    ≡⟨ p ⟩
      just x'
    ∎


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
    emp       = [] ;
    lkp       = lkp-aux ;
    add       = add-aux ;
    lkp-emp   = λ k → refl ;
    lkp-add-≡ = lkp-add-≡-aux ;
    lkp-add-≢ = lkp-add-≢-aux }

    where

      ---------
      -- lkp --
      ---------

      lkp-aux : List (Keys × A) → Keys → Maybe A
      lkp-aux [] k = nothing
      lkp-aux ((k' , x') ∷ d) k with test-keys k k'
      ... | yes p = just x'
      ... | no  p = lkp-aux d k

      ---------
      -- add --
      ---------

      add-aux : List (Keys × A) → Keys × A → List (Keys × A)
      add-aux [] (k , x) = (k , x) ∷ []
      add-aux ((k' , x') ∷ d) (k , x) with test-keys k k'
      ... | yes p = (k , x) ∷ d
      ... | no  p = (k' , x') ∷ add-aux d (k , x)

      ---------------
      -- lkp-add-≡ --
      ---------------

      lkp-add-≡-aux : (k : Keys) (x : A) (d : List (Keys × A))
                    → lkp-aux (add-aux d (k , x)) k ≡ just x
                    
      lkp-add-≡-aux k x [] rewrite (test-keys-refl k) = refl
      lkp-add-≡-aux k x ((k' , x') ∷ d) with test-keys k k' | inspect (uncurry test-keys) (k , k')
      ... | yes p | [ eq ] rewrite (test-keys-refl k) = refl
      ... | no  p | [ eq ] rewrite eq                 = lkp-add-≡-aux k x d

      ---------------
      -- lkp-add-≢ --
      ---------------

      lkp-add-≢-aux : (k k' : Keys) (x : A) (d : List (Keys × A))
                    → k ≢ k'
                    → lkp-aux (add-aux d (k , x)) k' ≡ lkp-aux d k'
                    
      lkp-add-≢-aux k k' x [] p rewrite test-keys-≢ k' k (p ∘ sym) = refl
      {- with test-keys k' k
      lkp-add-≢-aux k k' x [] p | yes q = ⊥-elim (p (sym q))
      lkp-add-≢-aux k k' x [] p | no  q = refl -}
      lkp-add-≢-aux k k' x ((k'' , x'') ∷ d) p with test-keys k k''
      lkp-add-≢-aux k k' x ((k'' , x'') ∷ d) p | yes refl rewrite test-keys-≢ k' k (p ∘ sym) = refl
      {- with test-keys k' k
      lkp-add-≢-aux k k' x ((k'' , x'') ∷ d) p | yes refl | yes r = ⊥-elim (p (sym r))
      lkp-add-≢-aux k k' x ((k'' , x'') ∷ d) p | yes refl | no  r = refl -}
      lkp-add-≢-aux k k' x ((k'' , x'') ∷ d) p | no q with test-keys k' k''
      lkp-add-≢-aux k k' x ((k'' , x'') ∷ d) p | no q | yes r = refl
      lkp-add-≢-aux k k' x ((k'' , x'') ∷ d) p | no q | no  r = lkp-add-≢-aux k k' x d p


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
    add-add-≡ = add-add-≡-aux }

    where

      open Dictionary (ListDict K A)

      ---------------
      -- add-add-≡ --
      ---------------

      add-add-≡-aux : (k : Keys) (x x' : A) (d : Dict)
                    → add (add d (k , x)) (k , x') ≡ add d (k , x')
                    
      add-add-≡-aux k x x' [] rewrite (test-keys-refl k) = refl
      add-add-≡-aux k x x' ((k'' , x'') ∷ d) with test-keys k k'' | inspect (uncurry test-keys) (k , k'')
      ... | yes p | [ eq ] rewrite (test-keys-refl k) = refl
      ... | no  p | [ eq ] rewrite eq                 = cong ((k'' , x'') ∷_) (add-add-≡-aux k x x' d)


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

{-
   Keys with a strict total preorder on them. The order `<ᴷ` is used
   below to define a version of `add` that satisfies `add-add-≢`.
-}

record OrdKey {l : Level} : Set (lsuc l) where
  field
    K' : Key {l}
  open Key K'
  field
    -- order relation
    _<ᴷ_      : Keys → Keys → Set
    -- irreflexivity
    <ᴷ-irrefl : {k : Keys} → k <ᴷ k → ⊥
    -- transitivity
    <ᴷ-trans  : {k₁ k₂ k₃ : Keys} → k₁ <ᴷ k₂ → k₂ <ᴷ k₃ → k₁ <ᴷ k₃
    -- totality
    <ᴷ-total  : (k₁ k₂ : Keys) → (k₁ <ᴷ k₂) ⊎ (k₂ <ᴷ k₁)
    -- proof irrelevance (all proofs of `k₁ <ᴷ k₂` are equal)
    <ᴷ-irrelevance : {k₁ k₂ : Keys} → (p q : k₁ <ᴷ k₂) → p ≡ q

  {-
     Some useful lemmas about how <ᴷ-total` computes under certain
     assumptions about the relationships of involved keys. These
     lemmas are useful below in combination with rewriting.
  -}

  <ᴷ-total-<ᴷ : (k k' : Keys) → (p : k <ᴷ k') → <ᴷ-total k k' ≡ inj₁ p
  <ᴷ-total-<ᴷ k k' p with <ᴷ-total k k'
  ... | inj₁ q = cong inj₁ (<ᴷ-irrelevance q p)
  ... | inj₂ q = ⊥-elim (<ᴷ-irrefl (<ᴷ-trans p q))

  <ᴷ-total-ᴷ> : (k k' : Keys) → (p : k' <ᴷ k) → <ᴷ-total k k' ≡ inj₂ p
  <ᴷ-total-ᴷ> k k' p with <ᴷ-total k k'
  ... | inj₁ q = ⊥-elim (<ᴷ-irrefl (<ᴷ-trans q p))
  ... | inj₂ q = cong inj₂ (<ᴷ-irrelevance q p)
    
{-
   This is a `Dictionary''` using the same `List (Keys × A)` type to
   store the key-value pairs. The main difference with `ListDict` and
   `ListDict'` defined above is the definition of `add`, which now
   uses the totality of `<ᴷ` to decide how to add the key-value pair
   into the dictionary if the given key wasn't already in the
   dictionary. While we do not prove it here explicitly, then
   `ListDict''` further satisfies the invariant that the `emp`, `add`,
   `lkp` operations keep the underlying dictionary data as a
   key-ordered list of key-value pairs (with no key repetition).
-}

module _ {l₁ l₂} (K : OrdKey {l₁}) (A : Set l₂) where

  open OrdKey K
  open Key K'
  open Dictionary'
  open Dictionary''

  {-
     The dictionary itself.
  -}

  ListDict'' : Dictionary'' K' A
  ListDict'' = record {
    Dict'' = record {
      Dict' = record {
        Dict = List (Keys × A) ;
        emp = [] ;
        lkp = lkp-aux ;
        add = add-aux ;
        lkp-emp = λ k → refl ;
        lkp-add-≡ = lkp-add-≡-aux ;
        lkp-add-≢ = lkp-add-≢-aux } ;
      add-add-≡ = add-add-≡-aux } ;
    add-add-≢ = add-add-≢-aux }

      where

        lkp-aux : List (Keys × A) → Keys → Maybe A
        lkp-aux [] k = nothing
        lkp-aux ((k' , x') ∷ d) k with test-keys k k'
        lkp-aux ((k' , x') ∷ d) k | yes p = just x'
        lkp-aux ((k' , x') ∷ d) k | no  p = lkp-aux d k

        add-aux : List (Keys × A) → Keys × A → List (Keys × A)
        add-aux [] (k , x) = (k , x) ∷ []
        add-aux ((k' , x') ∷ d) (k , x) with test-keys k k'
        add-aux ((k' , x') ∷ d) (k , x) | yes p = (k , x) ∷ d
        add-aux ((k' , x') ∷ d) (k , x) | no  p with <ᴷ-total k k'
        add-aux ((k' , x') ∷ d) (k , x) | no  p | inj₁ q = (k , x) ∷ (k' , x') ∷ d
        add-aux ((k' , x') ∷ d) (k , x) | no  p | inj₂ q = (k' , x') ∷ add-aux d (k , x)

        {-
           Warning: Don't be alarmed when you look at the proofs
           below.  They are long because they consider the various
           combinations of key equality testing and key order testing
           that we used in the definitions of`lkp` and `add` above.

           The use of rewriting and the above auxiliary lemmas about
           how `test-keys` and `<ᴷ-total` compute considerably cut
           down on redundant and repeating pattern-matching below.
        -}

        ---------------
        -- lkp-add-≡ --
        ---------------

        lkp-add-≡-aux : (k : Keys) (x : A) (d : List (Keys × A))
                      → lkp-aux (add-aux d (k , x)) k ≡ just x
                      
        lkp-add-≡-aux k x [] rewrite test-keys-refl k = refl
        lkp-add-≡-aux k x ((k' , x') ∷ d) with test-keys k k'
        lkp-add-≡-aux k x ((k' , x') ∷ d) | yes p rewrite test-keys-refl k = refl
        lkp-add-≡-aux k x ((k' , x') ∷ d) | no p with <ᴷ-total k k'
        lkp-add-≡-aux k x ((k' , x') ∷ d) | no p | inj₁ q rewrite test-keys-refl k   = refl
        lkp-add-≡-aux k x ((k' , x') ∷ d) | no p | inj₂ q rewrite test-keys-≢ k k' p = lkp-add-≡-aux k x d

        ---------------
        -- lkp-add-≢ --
        ---------------

        lkp-add-≢-aux : (k k' : Keys) (x : A) (d : List (Keys × A))
                      → k ≢ k'
                      → lkp-aux (add-aux d (k , x)) k' ≡ lkp-aux d k'
                      
        lkp-add-≢-aux k k' x [] p with test-keys k' k
        lkp-add-≢-aux k k' x [] p | yes q = ⊥-elim (p (sym q))
        lkp-add-≢-aux k k' x [] p | no  q = refl
        
        lkp-add-≢-aux k k' x ((k'' , x'') ∷ d) p with test-keys k k'' | test-keys k' k''
        lkp-add-≢-aux k k' x ((k'' , x'') ∷ d) p | yes q | yes r = ⊥-elim (p (trans q (sym r)))
        lkp-add-≢-aux k k' x ((k'' , x'') ∷ d) p | yes q | no  r with test-keys k' k
        lkp-add-≢-aux k k' x ((k'' , x'') ∷ d) p | yes q | no  r | yes s = ⊥-elim (p (sym s))
        lkp-add-≢-aux k k' x ((k'' , x'') ∷ d) p | yes q | no  r | no  s = refl
        lkp-add-≢-aux k k' x ((k'' , x'') ∷ d) p | no  q | yes r with <ᴷ-total k k''
        lkp-add-≢-aux k k' x ((k'' , x'') ∷ d) p | no  q | yes r | inj₁ s with test-keys k' k
        lkp-add-≢-aux k k' x ((k'' , x'') ∷ d) p | no  q | yes r | inj₁ s | yes t = ⊥-elim (q (trans (sym t) r))
        lkp-add-≢-aux k k' x ((k'' , x'') ∷ d) p | no  q | yes r | inj₁ s | no  t rewrite test-keys-≡ k' k'' r = refl
        lkp-add-≢-aux k k' x ((k'' , x'') ∷ d) p | no  q | yes r | inj₂ s rewrite test-keys-≡ k' k'' r = refl
        lkp-add-≢-aux k k' x ((k'' , x'') ∷ d) p | no  q | no  r with <ᴷ-total k k''
        lkp-add-≢-aux k k' x ((k'' , x'') ∷ d) p | no  q | no  r | inj₁ s with test-keys k' k
        lkp-add-≢-aux k k' x ((k'' , x'') ∷ d) p | no  q | no  r | inj₁ s | yes t = ⊥-elim (p (sym t))
        lkp-add-≢-aux k k' x ((k'' , x'') ∷ d) p | no  q | no  r | inj₁ s | no  t rewrite test-keys-≢ k' k'' r = refl
        lkp-add-≢-aux k k' x ((k'' , x'') ∷ d) p | no  q | no  r | inj₂ s rewrite test-keys-≢ k' k'' r = lkp-add-≢-aux k k' x d p

        ---------------
        -- add-add-≡ --
        ---------------

        add-add-≡-aux : (k : Keys) (x x' : A) (d : List (Keys × A))
                      → add-aux (add-aux d (k , x)) (k , x') ≡ add-aux d (k , x')
                      
        add-add-≡-aux k x x' [] rewrite test-keys-refl k = refl
        add-add-≡-aux k x x' ((k'' , x'') ∷ d) with test-keys k k''
        add-add-≡-aux k x x' ((k'' , x'') ∷ d) | yes p rewrite test-keys-refl k = refl
        add-add-≡-aux k x x' ((k'' , x'') ∷ d) | no  p with <ᴷ-total k k''
        add-add-≡-aux k x x' ((k'' , x'') ∷ d) | no  p | inj₁ q rewrite test-keys-refl k = refl
        add-add-≡-aux k x x' ((k'' , x'') ∷ d) | no  p | inj₂ q rewrite test-keys-≢ k k'' p
                                                                      | <ᴷ-total-ᴷ> k k'' q = cong ((k'' , x'') ∷_) (add-add-≡-aux k x x' d)

        ---------------
        -- add-add-≢ --
        ---------------

        add-add-≢-aux : (k k' : Keys) (x x' : A) (d : List (Keys × A))
                      → k ≢ k'
                      → add-aux (add-aux d (k , x)) (k' , x')
                        ≡
                        add-aux (add-aux d (k' , x')) (k , x)

        add-add-≢-aux k k' x x' [] p with test-keys k k'
        add-add-≢-aux k k' x x' [] p | yes q = ⊥-elim (p q)
        add-add-≢-aux k k' x x' [] p | no  q rewrite test-keys-≢ k' k (p ∘ sym) with <ᴷ-total k k'
        add-add-≢-aux k k' x x' [] p | no q | inj₁ r rewrite <ᴷ-total-ᴷ> k' k r = refl
        add-add-≢-aux k k' x x' [] p | no q | inj₂ r rewrite <ᴷ-total-<ᴷ k' k r = refl
        add-add-≢-aux k k' x x' ((k'' , x'') ∷ d) p with test-keys k k'' | test-keys k' k''
        add-add-≢-aux k k' x x' ((k'' , x'') ∷ d) p | yes q    | yes r = ⊥-elim (p (trans q (sym r)))
        add-add-≢-aux k k' x x' ((k'' , x'') ∷ d) p | yes q    | no  r with test-keys k' k
        add-add-≢-aux k k' x x' ((k'' , x'') ∷ d) p | yes q    | no  r | yes s = ⊥-elim (p (sym s))
        add-add-≢-aux k k' x x' ((k'' , x'') ∷ d) p | yes q    | no  r | no  s with <ᴷ-total k' k | <ᴷ-total k' k''
        add-add-≢-aux k k' x x' ((.k , x'') ∷ d)  p | yes refl | no  r | no  s | inj₁ t | inj₁ u rewrite test-keys-≢ k k' (r ∘ sym)
                                                                                                       | <ᴷ-total-ᴷ> k k' t
                                                                                                       | test-keys-refl k = refl
        add-add-≢-aux k k' x x' ((.k , x'') ∷ d) p  | yes refl | no  r | no  s | inj₁ t | inj₂ u = ⊥-elim (<ᴷ-irrefl (<ᴷ-trans u t))
        add-add-≢-aux k k' x x' ((.k , x'') ∷ d) p  | yes refl | no  r | no  s | inj₂ t | inj₁ u = ⊥-elim (<ᴷ-irrefl (<ᴷ-trans t u))
        add-add-≢-aux k k' x x' ((.k , x'') ∷ d) p  | yes refl | no  r | no  s | inj₂ t | inj₂ u rewrite test-keys-refl k = refl
        add-add-≢-aux k k' x x' ((.k' , x'') ∷ d) p | no  q    | yes refl with test-keys k k'
        add-add-≢-aux k k' x x' ((.k' , x'') ∷ d) p | no  q    | yes refl | yes s = ⊥-elim (p s)
        add-add-≢-aux k k' x x' ((.k' , x'') ∷ d) p | no  q    | yes refl | no  s with <ᴷ-total k k'
        add-add-≢-aux k k' x x' ((.k' , x'') ∷ d) p | no  q    | yes refl | no  s | inj₁ t rewrite test-keys-≢ k' k (p ∘ sym)
                                                                                                 | <ᴷ-total-ᴷ> k' k t
                                                                                                 | test-keys-refl k' = refl
        add-add-≢-aux k k' x x' ((.k' , x'') ∷ d) p | no  q    | yes refl | no  s | inj₂ t rewrite test-keys-refl k' = refl
        add-add-≢-aux k k' x x' ((k'' , x'') ∷ d) p | no  q    | no r with <ᴷ-total k k'' |  <ᴷ-total k' k''
        add-add-≢-aux k k' x x' ((k'' , x'') ∷ d) p | no  q    | no r | inj₁ s | inj₁ t rewrite test-keys-≢ k k' p
                                                                                             | test-keys-≢ k' k (p ∘ sym)
                                                                                        with <ᴷ-total k k'
        add-add-≢-aux k k' x x' ((k'' , x'') ∷ d) p | no  q    | no r | inj₁ s | inj₁ t | inj₁ u rewrite <ᴷ-total-ᴷ> k' k u
                                                                                                       | test-keys-≢ k' k'' r
                                                                                                       | <ᴷ-total-<ᴷ k' k'' t = refl
        add-add-≢-aux k k' x x' ((k'' , x'') ∷ d) p | no  q    | no r | inj₁ s | inj₁ t | inj₂ u rewrite <ᴷ-total-<ᴷ k' k u
                                                                                                       | test-keys-≢ k k'' q
                                                                                                       | <ᴷ-total-<ᴷ k k'' s = refl
        add-add-≢-aux k k' x x' ((k'' , x'') ∷ d) p | no  q    | no r | inj₁ s | inj₂ t rewrite test-keys-≢ k k'' q
                                                                                              | test-keys-≢ k' k (p ∘ sym)
                                                                                              | <ᴷ-total-<ᴷ k k'' s
                                                                                        with <ᴷ-total k' k
        add-add-≢-aux k k' x x' ((k'' , x'') ∷ d) p | no  q    | no r | inj₁ s | inj₂ t | inj₁ u = ⊥-elim (<ᴷ-irrefl (<ᴷ-trans s (<ᴷ-trans t u)))
        add-add-≢-aux k k' x x' ((k'' , x'') ∷ d) p | no  q    | no r | inj₁ s | inj₂ t | inj₂ u rewrite test-keys-≢ k' k'' r
                                                                                                       | <ᴷ-total-ᴷ> k' k'' t = refl
        add-add-≢-aux k k' x x' ((k'' , x'') ∷ d) p | no q     | no r | inj₂ s | inj₁ t rewrite test-keys-≢ k k' p
                                                                                             | test-keys-≢ k' k'' r
                                                                                             | <ᴷ-total-<ᴷ k' k'' t
                                                                                        with <ᴷ-total k k'
        add-add-≢-aux k k' x x' ((k'' , x'') ∷ d) p | no q     | no r | inj₂ s | inj₁ t | inj₁ u = ⊥-elim (<ᴷ-irrefl (<ᴷ-trans u (<ᴷ-trans t s)))
        add-add-≢-aux k k' x x' ((k'' , x'') ∷ d) p | no q     | no r | inj₂ s | inj₁ t | inj₂ u rewrite test-keys-≢ k k'' q
                                                                                                       | <ᴷ-total-ᴷ> k k'' s = refl
        add-add-≢-aux k k' x x' ((k'' , x'') ∷ d) p | no q     | no r | inj₂ s | inj₂ t rewrite test-keys-≢ k k'' q
                                                                                             | test-keys-≢ k' k'' r
                                                                                             | <ᴷ-total-ᴷ> k k'' s
                                                                                             | <ᴷ-total-ᴷ> k' k'' t = cong ((k'' , x'') ∷_) (add-add-≢-aux k k' x x' d p)

