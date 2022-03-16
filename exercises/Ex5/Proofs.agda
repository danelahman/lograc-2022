---------------------------------------------------------------------------
-- Week 5 exercises for the Logika v računalništvu course at UL FMF      --
-- Part 2 (Proofs using natural deduction for propositional logic)       --
--                                                                       --
-- Lecturer: Andrej Bauer                                                --
-- Teaching Assistant: Danel Ahman                                       --
--                                                                       --
-- Course website: https://ucilnica.fmf.uni-lj.si/course/view.php?id=252 --
-- Lecture notes: http://www.andrej.com/zapiski/ISRM-LOGRAC-2022/        --
---------------------------------------------------------------------------

{-
   Allowing overlapping instances for `∈` to use in `hyp`.

   Warning: If used carelessly, could lead to exponential
   slowdown and looping behaviour during instance search.
-}

{-# OPTIONS --overlapping-instances #-}

module Ex5.Proofs (AtomicFormula : Set) where

{-
   Importing the deeply embedded propositional logic together with its
   natural dediction proof system, parametrised by atomic formulae type.
-}

import Ex5.NaturalDeduction
open module ND = Ex5.NaturalDeduction AtomicFormula

{-
   Prove that the following statements hold in propositional logic
   using the natural deduction proof calculus defined in Part 1.

   To better visualise these proofs, you can "draw" the corresponding
   derivations on paper / in a comments block before typing them up.
-}


----------------
-- Exercise 3 --
----------------

{-
   First, show that `⇒` is functorial in both of its arguments:
   contravariant in first argument and covariant in second argument.
-}

⇒-contravariant : (φ ψ ξ : Formula)
                → [] ⊢ (φ ⇒ ψ) ⇒ (ψ ⇒ ξ) ⇒ φ ⇒ ξ
           
⇒-contravariant φ ψ ξ = {!!}

⇒-covariant : (φ ψ ξ : Formula)
            → [] ⊢ (φ ⇒ ψ) ⇒ (ξ ⇒ φ) ⇒ ξ ⇒ ψ
            
⇒-covariant φ ψ ξ = {!!}

{-
   Next, show that `⇒` and `∧` form an adjunction.
-}

⇒-∧-adjunction : (φ ψ ξ : Formula)
               → [] ⊢ (φ ⇒ ψ ⇒ ξ) ⇔ φ ∧ ψ ⇒ ξ
           
⇒-∧-adjunction φ ψ ξ = {!!}

{-
   Finally, show that `⇒` preserves `⊤` and `∧` in its second
   argument, exactly as expected of a right adjoint.
-}

⇒-preserves-⊤ : (φ : Formula)
              → [] ⊢ ⊤ ⇔ φ ⇒ ⊤

⇒-preserves-⊤ φ = {!!}

⇒-preserves-∧ : (φ ψ ξ : Formula)
              → [] ⊢ φ ⇒ ψ ∧ ξ ⇔ (φ ⇒ ψ) ∧ (φ ⇒ ξ)

⇒-preserves-∧ φ ψ ξ = {!!}


----------------
-- Exercise 4 --
----------------

{-
   Prove De Morgan's laws.
-}

{-
   This De Morgan's law holds in both directions in intuitionistic logic.
-}

demorgan₁₂ : (φ ψ : Formula)
           → [] ⊢ ¬ (φ ∨ ψ) ⇔ ¬ φ ∧ ¬ ψ

demorgan₁₂ φ ψ = {!!}

{-
   This De Morgan's law holds in only one direction in intuitionistic logic.
-}

demorgan₃ : (φ ψ : Formula)
          → [] ⊢ ¬ φ ∨ ¬ ψ ⇒ ¬ (φ ∧ ψ)

demorgan₃ φ ψ = {!!}

{-
   To prove the other direction of this De Morgan's law, we have to work in
   classical logic because it is not a tautology of intuitionistic logic.

   We do so by additionally assuming the Law of Excluded Middle (LEM).

   We can make such extra assumptions in two different ways:

   - at the meta-level in Agda, as in `demorgan₄` (this way we can assume
     LEM for arbitrary formulae `ξ`, corresponding to having the LEM
     axiom in the definition of the natural deduction proof system), or
   
   - hypothetically in the existing natural deduction proof system by 
     using a non-empty list of hypotheses, as in `demorgan₄'` (this way
     we can assume LEM for specific formulae, e.g., `φ` in `demorgan₄'`)
-}

demorgan₄ : (φ ψ : Formula)
          → (LEM : {Δ : Hypotheses} → (ξ : Formula) → Δ ⊢ ξ ∨ ¬ ξ)  -- LEM assumption
          → [] ⊢ ¬ (φ ∧ ψ) ⇒ ¬ φ ∨ ¬ ψ

demorgan₄ φ ψ LEM = {!!}

demorgan₄' : (φ ψ : Formula)
           → [ φ ∨ ¬ φ ] ⊢ ¬ (φ ∧ ψ) ⇒ ¬ φ ∨ ¬ ψ

demorgan₄' φ ψ = {!!}


----------------
-- Exercise 5 --
----------------

{-
   Show that LEM implies another of classical reasoning principles,
   the double negation elimination (DNE) rule, and vice versa.
-}

lem-dne : (φ : Formula)
        → (LEM : {Δ : Hypotheses} → (ξ : Formula) → Δ ⊢ ξ ∨ ¬ ξ)    -- LEM assumption
        → [] ⊢ ¬ ¬ φ ⇒ φ                                            -- DNE conclusion

lem-dne φ LEM = {!!}

dne-lem : (φ : Formula)
        → (DNE : {Δ : Hypotheses} → (ξ : Formula) → Δ ⊢ ¬ ¬ ξ ⇒ ξ)  -- DNE assumption
        → [] ⊢ φ ∨ ¬ φ                                              -- LEM conclusion

dne-lem φ DNE = {!!}
