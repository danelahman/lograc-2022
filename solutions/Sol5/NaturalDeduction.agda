------------------------------------------------------------------------------------
-- Solutions to Week 5 exercises for the Logika v računalništvu course at UL FMF  --
-- Part 1 (Natural deduction for intuitionistic propositional logic)              --
--                                                                                --
-- Lecturer: Andrej Bauer                                                         --
-- Teaching Assistant: Danel Ahman                                                --
--                                                                                --
-- Course website: https://ucilnica.fmf.uni-lj.si/course/view.php?id=252          --
-- Lecture notes: http://www.andrej.com/zapiski/ISRM-LOGRAC-2022/                 --
------------------------------------------------------------------------------------

{-
   Allowing overlapping instances for `∈` to use in `hyp`.

   Warning: If used carelessly, could lead to exponential
   slowdown and looping behaviour during instance search.
-}

{-# OPTIONS --overlapping-instances #-}

{-
   Notice that we parametrise the deeply embedded propositional logic
   and its natural deduction proof system over a type of atomic formulaes.
-}

module Sol5.NaturalDeduction (AtomicFormula : Set) where

open import Data.List  using (List; []; _∷_; [_]; _++_) public

{-
   Formulae of propositional logic.
-}

data Formula : Set where
  `_  : AtomicFormula → Formula           -- atomic formula
  ⊤   : Formula                           -- truth (unicode \top)
  ⊥   : Formula                           -- falsehood (unicode \bot)
  _∧_ : Formula → Formula → Formula       -- conjunction (unicode \wedge)
  _∨_ : Formula → Formula → Formula       -- disjunction (unicode \vee)
  _⇒_ : Formula → Formula → Formula       -- implication (unicode \=>)

infixr 6 _∧_
infixr 5 _∨_
infixr 4 _⇒_

{-
   Hypotheses are represented as a list of formulae.
-}

Hypotheses = List (Formula)

{-
   We use constructor instances when defining the formula-in-hypotheses
   membership relation `∈`. This way we will be able to use instance
   search to fill in these arguments when constructing derivations.

   Note: Agda will report an error if instance search is used to try to
   provide a witness of `{{x ∈ xs}}` when `xs` contains multiple copies
   of `x`, because in that case there isn't a unique proof of `x ∈ xs`.
   In those cases you can provide an explicit proof of the form `{{p}}`.

   You shouldn't be running into such errors in this week's exercises
   as their most concise solutions will involve repeated hypotheses.
-}

infix 3 _∈_
data _∈_ {A : Set} : A → List A → Set where
  instance
    ∈-here  : {x : A} → {xs : List A} → x ∈ (x ∷ xs)
    ∈-there : {x y : A} {xs : List A} → {{x ∈ xs}} → x ∈ (y ∷ xs)

{-
   Below is a natural deduction style proof calculus for **intuitionistic**
   propositional logic, formalised as an inductive relation.
-}

infixl 2 _⊢_
data _⊢_ : (Δ : Hypotheses) → (φ : Formula) → Set where    -- unicode \vdash

  -- structural rules

  weaken   : {Δ₁ Δ₂ : Hypotheses}
           → (φ : Formula)
           → {ψ : Formula}
           → Δ₁ ++ Δ₂ ⊢ ψ
           -----------------------
           → Δ₁ ++ [ φ ] ++ Δ₂ ⊢ ψ

  contract : {Δ₁ Δ₂ : Hypotheses}
           → (φ : Formula)
           → {ψ : Formula}
           → Δ₁ ++ [ φ ] ++ [ φ ] ++ Δ₂ ⊢ ψ
           --------------------------------
           → Δ₁ ++ [ φ ] ++ Δ₂ ⊢ ψ

  exchange : {Δ₁ Δ₂ : Hypotheses}
           → (φ₁ φ₂ : Formula)
           → {ψ : Formula}
           → Δ₁ ++ [ φ₁ ] ++ [ φ₂ ] ++ Δ₂ ⊢ ψ
           -----------------------------------------
           → Δ₁ ++ [ φ₂ ] ++ [ φ₁ ] ++ Δ₂ ⊢ ψ

  -- hypotheses

  hyp      : {Δ : Hypotheses}
           → (φ : Formula)
           → {{φ ∈ Δ}}
           -----------------
           → Δ ⊢ φ

  -- truth

  ⊤-intro  : {Δ : Hypotheses}
           ------------------
           → Δ ⊢ ⊤

  -- falsehood

  ⊥-elim   : {Δ : Hypotheses}
           → {φ : Formula}
           → Δ ⊢ ⊥
           -------------------
           → Δ ⊢ φ

  -- conjunction

  ∧-intro  : {Δ : Hypotheses}
           → {φ ψ : Formula}
           → Δ ⊢ φ
           → Δ ⊢ ψ
           -------------------
           → Δ ⊢ φ ∧ ψ
          
  ∧-elim₁  : {Δ : Hypotheses}
           → {φ ψ : Formula}
           → Δ ⊢ φ ∧ ψ
           -------------------
           → Δ ⊢ φ

  ∧-elim₂  : {Δ : Hypotheses}
           → {φ ψ : Formula}
           → Δ ⊢ φ ∧ ψ
           -------------------
           → Δ ⊢ ψ

  -- disjunction

  ∨-intro₁ : {Δ : Hypotheses}
           → {φ ψ : Formula}
           → Δ ⊢ φ
           ------------------
           → Δ ⊢ φ ∨ ψ

  ∨-intro₂ : {Δ : Hypotheses}
           → {φ ψ : Formula}
           → Δ ⊢ ψ
           -------------------
           → Δ ⊢ φ ∨ ψ

  ∨-elim   : {Δ : Hypotheses}
           → {φ₁ φ₂ ψ : Formula}
           → Δ ⊢ φ₁ ∨ φ₂
           → Δ ++ [ φ₁ ] ⊢ ψ
           → Δ ++ [ φ₂ ] ⊢ ψ
           ---------------------
           → Δ ⊢ ψ

  -- implication

  ⇒-intro  : {Δ : Hypotheses}
           → {φ ψ : Formula}
           → Δ ++ [ φ ] ⊢ ψ
           --------------------
           → Δ ⊢ φ ⇒ ψ

  ⇒-elim   : {Δ : Hypotheses}
           → {φ ψ : Formula}
           → Δ ⊢ φ ⇒ ψ
           → Δ ⊢ φ
           -------------------
           → Δ ⊢ ψ

{-
   We define negation and logical equivalence as syntactic sugar.
   These definitions are standard logical encodings of `¬` and `⇔`.
-}

¬_ : Formula → Formula              -- unicode \neg
¬ φ = φ ⇒ ⊥

_⇔_ : Formula → Formula → Formula    -- unicode \<=>
φ ⇔ ψ = (φ ⇒ ψ) ∧ (ψ ⇒ φ)

infix 7 ¬_
infix 3 _⇔_


----------------
-- Exercise 1 --
----------------

{-
   Show that the standard introduction and elimination rules of `¬`
   are derivable for the logical encoding of `¬` defined above.
-}

¬-intro : {Δ : Hypotheses}
        → {φ : Formula}
        → Δ ++ [ φ ] ⊢ ⊥
        → Δ ⊢ ¬ φ

¬-intro d = ⇒-intro d

¬-elim : {Δ : Hypotheses}
       → {φ : Formula}
       → Δ ⊢ φ
       → Δ ⊢ ¬ φ
       → Δ ⊢ ⊥

¬-elim d₁ d₂ = ⇒-elim d₂ d₁

{-
   Show that the last rule is also derivable when the assumptions
   about `φ` and `¬ φ` being true are given as part of hypotheses.
-}

¬-elim' : (φ : Formula)
        → [ φ ] ++ [ ¬ φ ] ⊢ ⊥

¬-elim' φ = ⇒-elim (hyp (¬ φ)) (hyp φ)


----------------
-- Exercise 2 --
----------------

{-
   Show that the cut rule is derivable in the above natural deduction
   system (by using the intro/elim-rules of other logical connectives).

   Note 1: There are more than one possible derivations of the cut rule.

   Note 2: While here the richness of our logic (i.e., the other logical
   connectives) allows us to simply **derive** the cut rule as a single
   concrete derivation, in more general settings one usually shows the
   **admissibility** of the cut rule by induction on the (heights of)
   the given derivations, e.g., see https://www.jstor.org/stable/420956.
-}

cut-derivable : {Δ : Hypotheses}
              → {φ ψ : Formula}
              → Δ ⊢ φ
              → Δ ++ [ φ ] ⊢ ψ
              ------------------
              → Δ ⊢ ψ

cut-derivable d₁ d₂ = ⇒-elim (⇒-intro d₂) d₁


--------------------
-- Bonus Exercise --
--------------------

{-
   Show that (in addition to cut) the other three structural rules
   (weakening, contraction, and exchange) are also admissible.

   For this it is best to create a copy of this file, remove these
   three rules, and then define functions with corresponding types.

   Hint: Instead of trying to define the functions corresponding to
   these structural rules directly by induction on the given natural
   deduction derivation, another approach would be to define general
   renamings between contexts of hypothesis, together with their
   action on derivations, and then use this action to apply suitable
   renamings to a derivation to recover the three structural rules.
-}
