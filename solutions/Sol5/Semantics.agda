------------------------------------------------------------------------------------
-- Solutions to Week 5 exercises for the Logika v računalništvu course at UL FMF  --
-- Part 3 (Semantics of propositional logic)                                      --
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

module Sol5.Semantics (AtomicFormula : Set) where

{-
   Imports from the standard library.
-}

open import Data.Bool renaming (_∧_ to _and_; _∨_ to _or_) -- note these renamings; the corresponding lemmas
                                                           -- are still called `∧-something` and `∨-something`
open import Data.Bool.Properties
open import Data.Product

import Relation.Binary.PropositionalEquality as Eq
open Eq renaming ([_] to [|_|])
open Eq.≡-Reasoning

{-
   Importing the deeply embedded propositional logic together with its
   natural dediction proof system, parametrised by atomic formulae type.
-}

import Sol5.NaturalDeduction
open module ND = Sol5.NaturalDeduction AtomicFormula

{-
   Importing a custom inequational reasoning module that provides a
   `beginᵇ` and `∎ᵇ` style reasoning for the `≤` relation on `Bool`.

   A typical proof with this equational reasoning machinery looks like

     beginᵇ
       lhs
     ≤⟨ reason why `lhs ≤ intermediate-result` ⟩
       intermediate-result
     ≡ᵇ⟨ reason why `intermediate-result ≡ rhs` ⟩
       rhs
     ∎ᵇ

   Notice the superscript `ᵇ` to distinguish this reasoning from
   `begin` and `∎` style equational reasoning for `≡`. You can
   get the superscript symbol `ᵇ` in unicode by typing \^b.
-}

open import Sol5.≤-Reasoning

{-
   The universe of truth values into which we interpret our logic.

   As we are interpreting propositional logic, we shall just use
   booleans. For predicate logics (e.g., in your projects), you will
   want to choose something different as the interpretation target.

   While the propositional logic we interpret is intuitionistic,
   this boolean semantics also models classical logical axioms.
   We will make this claim precise in Exercise 9 below.
-}

ℙ = Bool   -- unicode \bP

{-
   Environments/valuations assigning truth values to atomic formulae.
-}

Env = AtomicFormula → ℙ


----------------
-- Exercise 6 --
----------------

{-
   Define logical implication between boolean values.
-}

_implies_ : ℙ → ℙ → ℙ
b₁ implies b₂ = not b₁ or b₂

{-
   The recursively defined interpretation function for formulae.

   Connectives of the logic are mapped to the standard boolean
   algebra operations on the type `ℙ = Bool` of booleans.
-}

⟦_⟧ : Formula → Env → ℙ                 -- unicode \[[ \]]
⟦ ` P ⟧   η = η P
⟦ ⊤ ⟧     η = true
⟦ ⊥ ⟧     η = false
⟦ φ ∧ ψ ⟧ η = ⟦ φ ⟧ η and ⟦ ψ ⟧ η
⟦ φ ∨ ψ ⟧ η = ⟦ φ ⟧ η or ⟦ ψ ⟧ η
⟦ φ ⇒ ψ ⟧ η = ⟦ φ ⟧ η implies ⟦ ψ ⟧ η

{-
   The interpretation function is also extended to hypotheses.
-}

⟦_⟧ₑ : Hypotheses → Env → ℙ             -- unicode \[[ \]] \_e
⟦ [] ⟧ₑ    η = true
⟦ φ ∷ Δ ⟧ₑ η = ⟦ φ ⟧ η and ⟦ Δ ⟧ₑ η

{-
   Below are some useful lemmas concerning the interpretation and `≤`.

   Hint: To finish the soundness proof below, you will likely need to
   prove some additional analogous lemmas also for `∨` and `≤`.
-}

⟦⟧ₑ-++ : (Δ₁ Δ₂ : Hypotheses) {η : Env}
       → ⟦ Δ₁ ++ Δ₂ ⟧ₑ η ≡ ⟦ Δ₁ ⟧ₑ η and ⟦ Δ₂ ⟧ₑ η

⟦⟧ₑ-++ [] Δ₂ {η} = 
  begin
    ⟦ [] ++ Δ₂ ⟧ₑ η
  ≡⟨⟩
    ⟦ [] ⟧ₑ η and ⟦ Δ₂ ⟧ₑ η
  ∎
⟦⟧ₑ-++ (φ ∷ Δ₁) Δ₂ {η} =
  begin
    ⟦ (φ ∷ Δ₁) ++ Δ₂ ⟧ₑ η
  ≡⟨⟩
    ⟦ φ ⟧ η and ⟦ Δ₁ ++ Δ₂ ⟧ₑ η
  ≡⟨ cong (⟦ φ ⟧ η and_) (⟦⟧ₑ-++ Δ₁ Δ₂) ⟩
    ⟦ φ ⟧ η and ⟦ Δ₁ ⟧ₑ η and ⟦ Δ₂ ⟧ₑ η
  ≡⟨ sym (∧-assoc (⟦ φ ⟧ η) (⟦ Δ₁ ⟧ₑ η) (⟦ Δ₂ ⟧ₑ η)) ⟩
    (⟦ φ ⟧ η and ⟦ Δ₁ ⟧ₑ η) and ⟦ Δ₂ ⟧ₑ η
  ≡⟨⟩
    ⟦ φ ∷ Δ₁ ⟧ₑ η and ⟦ Δ₂ ⟧ₑ η
  ∎

----

and-cong : {b₁ b₂ b₃ b₄ : Bool}
          → b₁ ≤ b₃
          → b₂ ≤ b₄
          → b₁ and b₂ ≤ b₃ and b₄

and-cong f≤t f≤t =
  beginᵇ
    false
  ≤⟨ f≤t ⟩
    true
  ∎ᵇ
and-cong {_} {b₂} f≤t b≤b =
  beginᵇ
    false and b₂
  ≤⟨ ≤-minimum b₂ ⟩
    true and b₂
  ∎ᵇ
and-cong {b₁} b≤b f≤t =
  beginᵇ
    b₁ and false
  ≡ᵇ⟨ ∧-comm b₁ false ⟩
    false
  ≤⟨ ≤-minimum (b₁ and true) ⟩
    b₁ and true
  ∎ᵇ
and-cong {b₁} {b₂} b≤b b≤b =
  beginᵇ
    b₁ and b₂
  ≡ᵇ⟨ refl ⟩
    b₁ and b₂
  ∎ᵇ

----

and-cong₁ : {b₁ b₂ b₃ : Bool}
          → b₁ ≤ b₂
          → b₁ and b₃ ≤ b₂ and b₃
              
and-cong₁ p = and-cong p ≤-refl

----

and-cong₂ : {b₁ b₂ b₃ : Bool}
          → b₂ ≤ b₃
          → b₁ and b₂ ≤ b₁ and b₃

and-cong₂ p = and-cong ≤-refl p

----

and-proj₁ : (b₁ b₂ : Bool)
          → b₁ and b₂ ≤ b₁

and-proj₁ false b₂ =
  beginᵇ
    false and b₂
  ≤⟨ ≤-refl ⟩
    false
  ∎ᵇ
and-proj₁ true  b₂ =
  beginᵇ
    true and b₂
  ≤⟨ ≤-maximum b₂ ⟩
    true
  ∎ᵇ

----

and-proj₂ : (b₁ b₂ : Bool)
          → b₁ and b₂ ≤ b₂

and-proj₂ b₁ b₂ =
  beginᵇ
    b₁ and b₂
  ≡ᵇ⟨ ∧-comm b₁ b₂ ⟩
    b₂ and b₁
  ≤⟨ and-proj₁ b₂ b₁ ⟩
    b₂
  ∎ᵇ

----

or-inj₁ : (b₁ b₂ : Bool)
        → b₁ ≤ b₁ or b₂
          
or-inj₁ b₁ false =
  beginᵇ
    b₁
  ≤⟨⟩
    b₁
  ≡ᵇ⟨ ∨-comm false b₁ ⟩
    b₁ or false
  ∎ᵇ
or-inj₁ b₁ true = 
  beginᵇ
    b₁
  ≤⟨ ≤-maximum b₁ ⟩
    true
  ≡ᵇ⟨ ∨-comm true b₁ ⟩
    b₁ or true
  ∎ᵇ

----

or-inj₂ : (b₁ b₂ : Bool)
        → b₂ ≤ b₁ or b₂

or-inj₂ b₁ b₂ =
  beginᵇ
    b₂
  ≤⟨ or-inj₁ b₂ b₁ ⟩
    b₂ or b₁
  ≡ᵇ⟨ ∨-comm b₂ b₁ ⟩
    b₁ or b₂
  ∎ᵇ

----

or-cong : {b₁ b₂ b₃ b₄ : Bool}
        → b₁ ≤ b₃
        → b₂ ≤ b₄
        → b₁ or b₂ ≤ b₃ or b₄
        
or-cong {_} {b₂} {_} {b₄} f≤t q =
  beginᵇ
    false or b₂
  ≤⟨ ≤-maximum b₂ ⟩
    true or b₄
  ∎ᵇ
or-cong {b₁} b≤b f≤t =
  beginᵇ
    b₁ or false
  ≤⟨ ≤-maximum (b₁ or false) ⟩
    true
  ≡ᵇ⟨ ∨-comm true b₁ ⟩
    b₁ or true
  ∎ᵇ
or-cong {b₁} {b₂} b≤b b≤b =
  beginᵇ
    b₁ or b₂
  ≤⟨ ≤-refl ⟩
    b₁ or b₂
  ∎ᵇ

----

contradiction : (b : Bool)
              → not b and b ≡ false
              
contradiction false = refl
contradiction true  = refl


---------------------------------
-- Soundness of interpretation --
---------------------------------

{-
   In the last two exercises, we shall prove that the interpretation
   function `⟦-⟧` we defined above is sound with respect to derivability.

   We shall prove that if we are given a derivation of the judgment `Δ ⊢ φ`
   in our natural deduction proof system, then for any environment/valuation
   `η` modelling the truth/falsehood of atomic formulae, we have that:

     - if `⟦ Δ ⟧ₑ η` evaluates to `true`, then `⟦ φ ⟧ η` evaluates to `true` as well

   We capture this hypothetical statement using the less than or equal
   relation `≤` (unicode \le) on booleans, defined in `Data.Bool.Base`,
   which holds if one of the following two conditions holds:

     - `false ≤ true`
     
     - `b     ≤ b`            (for any boolean value `b`)

   Using `≤`, the above soundness statement becomes

     - `⟦ Δ ⟧ₑ η ≤ ⟦ φ ⟧ η`

   For proving such inequations, you will find many useful lemmas 
   proved in the `Data.Bool.Properties` module imported from stdlib.
-}


----------------
-- Exercise 7 --
----------------

{-
   Finish the proof of the soundness theorem below, where some
   of the cases are already filled in to help you start going.
-}

soundness : {Δ : Hypotheses}
          → {φ : Formula}
          → Δ ⊢ φ
          → {η : Env}
          → ⟦ Δ ⟧ₑ η ≤ ⟦ φ ⟧ η

soundness (weaken {Δ₁} {Δ₂} φ {ψ} d) {η} =
  beginᵇ
    ⟦ Δ₁ ++ [ φ ] ++ Δ₂ ⟧ₑ η
  ≡ᵇ⟨ ⟦⟧ₑ-++ Δ₁ ([ φ ] ++ Δ₂) ⟩
    ⟦ Δ₁ ⟧ₑ η and ⟦ [ φ ] ++ Δ₂ ⟧ₑ η
  ≤⟨⟩
    ⟦ Δ₁ ⟧ₑ η and ⟦ φ ⟧ η and ⟦ Δ₂ ⟧ₑ η
  ≤⟨ and-cong₂ (and-proj₂ (⟦ φ ⟧ η) (⟦ Δ₂ ⟧ₑ η)) ⟩
    ⟦ Δ₁ ⟧ₑ η and ⟦ Δ₂ ⟧ₑ η
  ≡ᵇ⟨ sym (⟦⟧ₑ-++ Δ₁ Δ₂) ⟩
    ⟦ Δ₁ ++ Δ₂ ⟧ₑ η
  ≤⟨ soundness d ⟩
    ⟦ ψ ⟧ η
  ∎ᵇ
    
soundness (contract {Δ₁} {Δ₂} φ {ψ} d) {η} =
  beginᵇ
    ⟦ Δ₁ ++ [ φ ] ++ Δ₂ ⟧ₑ η
  ≡ᵇ⟨ ⟦⟧ₑ-++ Δ₁ ([ φ ] ++ Δ₂) ⟩
    ⟦ Δ₁ ⟧ₑ η and ⟦ φ ⟧ η and ⟦ Δ₂ ⟧ₑ η
  ≡ᵇ⟨ cong (λ b → ⟦ Δ₁ ⟧ₑ η and b and ⟦ Δ₂ ⟧ₑ η) (sym (∧-idem (⟦ φ ⟧ η))) ⟩
    ⟦ Δ₁ ⟧ₑ η and (⟦ φ ⟧ η and ⟦ φ ⟧ η) and ⟦ Δ₂ ⟧ₑ η
  ≡ᵇ⟨ cong (⟦ Δ₁ ⟧ₑ η and_) (∧-assoc (⟦ φ ⟧ η) (⟦ φ ⟧ η) (⟦ Δ₂ ⟧ₑ η)) ⟩
    ⟦ Δ₁ ⟧ₑ η and ⟦ φ ⟧ η and ⟦ φ ⟧ η and ⟦ Δ₂ ⟧ₑ η
  ≡ᵇ⟨ sym (⟦⟧ₑ-++ Δ₁ ([ φ ] ++ [ φ ] ++ Δ₂)) ⟩
    ⟦ Δ₁ ++ [ φ ] ++ [ φ ] ++ Δ₂ ⟧ₑ η
  ≤⟨ soundness d ⟩
    ⟦ ψ ⟧ η
  ∎ᵇ

soundness (exchange {Δ₁} {Δ₂} φ₁ φ₂ {ψ} d) {η} =
  beginᵇ
    ⟦ Δ₁ ++ [ φ₂ ] ++ [ φ₁ ] ++ Δ₂ ⟧ₑ η
  ≡ᵇ⟨ ⟦⟧ₑ-++ Δ₁ ([ φ₂ ] ++ [ φ₁ ] ++ Δ₂) ⟩
    ⟦ Δ₁ ⟧ₑ η and ⟦ φ₂ ⟧ η and ⟦ φ₁ ⟧ η and ⟦ Δ₂ ⟧ₑ η
  ≡ᵇ⟨ cong (⟦ Δ₁ ⟧ₑ η and_) (sym (∧-assoc (⟦ φ₂ ⟧ η) (⟦ φ₁ ⟧ η) (⟦ Δ₂ ⟧ₑ η))) ⟩
    ⟦ Δ₁ ⟧ₑ η and (⟦ φ₂ ⟧ η and ⟦ φ₁ ⟧ η) and ⟦ Δ₂ ⟧ₑ η
  ≡ᵇ⟨ cong (λ b → ⟦ Δ₁ ⟧ₑ η and b and ⟦ Δ₂ ⟧ₑ η) (∧-comm (⟦ φ₂ ⟧ η) (⟦ φ₁ ⟧ η)) ⟩
    ⟦ Δ₁ ⟧ₑ η and (⟦ φ₁ ⟧ η and ⟦ φ₂ ⟧ η) and ⟦ Δ₂ ⟧ₑ η
  ≡ᵇ⟨ cong (⟦ Δ₁ ⟧ₑ η and_) (∧-assoc (⟦ φ₁ ⟧ η) (⟦ φ₂ ⟧ η) (⟦ Δ₂ ⟧ₑ η)) ⟩
    ⟦ Δ₁ ⟧ₑ η and ⟦ φ₁ ⟧ η and ⟦ φ₂ ⟧ η and ⟦ Δ₂ ⟧ₑ η
  ≡ᵇ⟨ sym (⟦⟧ₑ-++ Δ₁ ([ φ₁ ] ++ [ φ₂ ] ++ Δ₂)) ⟩
    ⟦ Δ₁ ++ [ φ₁ ] ++ [ φ₂ ] ++ Δ₂ ⟧ₑ η
  ≤⟨ soundness d ⟩
    ⟦ ψ ⟧ η
  ∎ᵇ

soundness (hyp {φ ∷ Δ} φ {{ ∈-here }}) {η} =
  beginᵇ
    ⟦ φ ⟧ η and ⟦ Δ ⟧ₑ η
  ≤⟨ and-proj₁ (⟦ φ ⟧ η) (⟦ Δ ⟧ₑ η) ⟩
    ⟦ φ ⟧ η
  ∎ᵇ
soundness (hyp {ψ ∷ Δ} φ {{ (∈-there {{ p }}) }}) {η} =
  beginᵇ
    ⟦ ψ ⟧ η and ⟦ Δ ⟧ₑ η
  ≤⟨ and-proj₂ (⟦ ψ ⟧ η) (⟦ Δ ⟧ₑ η) ⟩
    ⟦ Δ ⟧ₑ η
  ≤⟨ soundness (hyp φ {{ p }}) ⟩
    ⟦ φ ⟧ η
  ∎ᵇ

soundness (⊤-intro {Δ}) {η} =
  beginᵇ
    ⟦ Δ ⟧ₑ η
  ≤⟨ ≤-maximum (⟦ Δ ⟧ₑ η) ⟩
    ⟦ ⊤ ⟧ η
  ∎ᵇ

soundness (⊥-elim {Δ} {φ} d) {η} =
  beginᵇ
    ⟦ Δ ⟧ₑ η
  ≤⟨ soundness d ⟩
    false
  ≤⟨ ≤-minimum (⟦ φ ⟧ η) ⟩
    ⟦ φ ⟧ η
  ∎ᵇ

soundness (∧-intro {Δ} {φ} {ψ} d₁ d₂) {η} =
  beginᵇ
    ⟦ Δ ⟧ₑ η
  ≡ᵇ⟨ sym (∧-idem (⟦ Δ ⟧ₑ η)) ⟩
    ⟦ Δ ⟧ₑ η and ⟦ Δ ⟧ₑ η
  ≤⟨ and-cong (soundness d₁) (soundness d₂) ⟩
    ⟦ φ ⟧ η and ⟦ ψ ⟧ η
  ∎ᵇ

soundness (∧-elim₁ {Δ} {φ} {ψ} d) {η} =
  beginᵇ
    ⟦ Δ ⟧ₑ η
  ≤⟨ soundness d ⟩
    ⟦ φ ⟧ η and ⟦ ψ ⟧ η
  ≤⟨ and-proj₁ (⟦ φ ⟧ η) (⟦ ψ ⟧ η) ⟩
    ⟦ φ ⟧ η
  ∎ᵇ

soundness (∧-elim₂ {Δ} {φ} {ψ} d) {η} =
  beginᵇ
    ⟦ Δ ⟧ₑ η
  ≤⟨ soundness d ⟩
    ⟦ φ ⟧ η and ⟦ ψ ⟧ η
  ≤⟨ and-proj₂ (⟦ φ ⟧ η) (⟦ ψ ⟧ η) ⟩
    ⟦ ψ ⟧ η
  ∎ᵇ

soundness (∨-intro₁ {Δ} {φ} {ψ} d) {η} =
  beginᵇ
    ⟦ Δ ⟧ₑ η
  ≤⟨ soundness d ⟩
    ⟦ φ ⟧ η
  ≤⟨ or-inj₁ (⟦ φ ⟧ η) (⟦ ψ ⟧ η) ⟩
    ⟦ φ ⟧ η or ⟦ ψ ⟧ η
  ∎ᵇ

soundness (∨-intro₂ {Δ} {φ} {ψ} d) {η} =
  beginᵇ
    ⟦ Δ ⟧ₑ η
  ≤⟨ soundness d ⟩
    ⟦ ψ ⟧ η
  ≤⟨ or-inj₂ (⟦ φ ⟧ η) (⟦ ψ ⟧ η) ⟩
    ⟦ φ ⟧ η or ⟦ ψ ⟧ η
  ∎ᵇ

soundness (∨-elim {Δ} {φ₁} {φ₂} {ψ} d₁ d₂ d₃) {η} =
  beginᵇ
    ⟦ Δ ⟧ₑ η
  ≡ᵇ⟨ sym (∧-idem (⟦ Δ ⟧ₑ η)) ⟩
    ⟦ Δ ⟧ₑ η and ⟦ Δ ⟧ₑ η
  ≤⟨ and-cong₂ (soundness d₁) ⟩
    ⟦ Δ ⟧ₑ η and (⟦ φ₁ ⟧ η or ⟦ φ₂ ⟧ η)
  ≡ᵇ⟨ ∧-distribˡ-∨ (⟦ Δ ⟧ₑ η) (⟦ φ₁ ⟧ η) (⟦ φ₂ ⟧ η) ⟩
    (⟦ Δ ⟧ₑ η and ⟦ φ₁ ⟧ η) or (⟦ Δ ⟧ₑ η and ⟦ φ₂ ⟧ η)
  ≤⟨ or-cong
       (beginᵇ
          ⟦ Δ ⟧ₑ η and ⟦ φ₁ ⟧ η
        ≡ᵇ⟨ cong (⟦ Δ ⟧ₑ η and_) (sym (∧-identityʳ (⟦ φ₁ ⟧ η))) ⟩
          ⟦ Δ ⟧ₑ η and ⟦ φ₁ ⟧ η and true
        ≡ᵇ⟨ sym (⟦⟧ₑ-++ Δ [ φ₁ ]) ⟩
          ⟦ Δ ++ [ φ₁ ] ⟧ₑ η
        ≤⟨ soundness d₂ ⟩
          ⟦ ψ ⟧ η
        ∎ᵇ)
       (beginᵇ
          ⟦ Δ ⟧ₑ η and ⟦ φ₂ ⟧ η
        ≡ᵇ⟨ cong (⟦ Δ ⟧ₑ η and_) (sym (∧-identityʳ (⟦ φ₂ ⟧ η))) ⟩
          ⟦ Δ ⟧ₑ η and ⟦ φ₂ ⟧ η and true
        ≡ᵇ⟨ sym (⟦⟧ₑ-++ Δ [ φ₂ ]) ⟩
          ⟦ Δ ++ [ φ₂ ] ⟧ₑ η
        ≤⟨ soundness d₃ ⟩
          ⟦ ψ ⟧ η
        ∎ᵇ) ⟩
    ⟦ ψ ⟧ η or ⟦ ψ ⟧ η
  ≡ᵇ⟨ ∨-idem (⟦ ψ ⟧ η) ⟩
    ⟦ ψ ⟧ η
  ∎ᵇ

soundness (⇒-intro {Δ} {φ} {ψ} d) {η} with ⟦ φ ⟧ η | inspect (λ (φ , η) → ⟦ φ ⟧ η) (φ , η)  -- use of LEM in the boolean semantics
... | false | [| eq |] =
  beginᵇ
    ⟦ Δ ⟧ₑ η
  ≤⟨ ≤-maximum (⟦ Δ ⟧ₑ η) ⟩
    true
  ∎ᵇ
... | true  | [| eq |] =
  beginᵇ
    ⟦ Δ ⟧ₑ η
  ≡ᵇ⟨ sym (∧-idem (⟦ Δ ⟧ₑ η)) ⟩
    ⟦ Δ ⟧ₑ η and ⟦ Δ ⟧ₑ η
  ≤⟨  and-cong ≤-refl (≤-trans (≤-maximum (⟦ Δ ⟧ₑ η)) (≤-≡ (sym eq))) ⟩
    ⟦ Δ ⟧ₑ η and ⟦ φ ⟧ η
  ≡ᵇ⟨ cong (⟦ Δ ⟧ₑ η and_) (sym (∧-identityʳ (⟦ φ ⟧ η))) ⟩
    ⟦ Δ ⟧ₑ η and ⟦ φ ⟧ η and true
  ≡ᵇ⟨ sym (⟦⟧ₑ-++ Δ [ φ ]) ⟩
    ⟦ Δ ++ [ φ ] ⟧ₑ η
  ≤⟨ soundness d ⟩
    ⟦ ψ ⟧ η
  ∎ᵇ

soundness (⇒-elim {Δ} {φ} {ψ} d₁ d₂) {η} =
  beginᵇ
    ⟦ Δ ⟧ₑ η
  ≡ᵇ⟨ sym (∧-idem (⟦ Δ ⟧ₑ η)) ⟩
    ⟦ Δ ⟧ₑ η and ⟦ Δ ⟧ₑ η
  ≤⟨ and-cong (soundness d₁) (soundness d₂) ⟩
    (not (⟦ φ ⟧ η) or ⟦ ψ ⟧ η) and ⟦ φ ⟧ η
  ≡ᵇ⟨ ∧-distribʳ-∨ (⟦ φ ⟧ η) (not (⟦ φ ⟧ η)) (⟦ ψ ⟧ η) ⟩
    (not (⟦ φ ⟧ η) and ⟦ φ ⟧ η) or (⟦ ψ ⟧ η and ⟦ φ ⟧ η)
  ≡ᵇ⟨ cong (_or (⟦ ψ ⟧ η and ⟦ φ ⟧ η)) (contradiction (⟦ φ ⟧ η)) ⟩
    false or (⟦ ψ ⟧ η and ⟦ φ ⟧ η)
  ≤⟨⟩
   ⟦ ψ ⟧ η and ⟦ φ ⟧ η
  ≤⟨ and-proj₁ (⟦ ψ ⟧ η) (⟦ φ ⟧ η) ⟩
    ⟦ ψ ⟧ η
  ∎ᵇ


----------------
-- Exercise 8 --
----------------

{-
   Prove the consistency theorem for the natural deduction proof system.

   Specifically, show that it is not possible to prove `⊥` from an empty
   list of hypotheses using the proof system defined in Part 1.

   Hint: This is simplest to do using the semantics defined above.
-}

open import Data.Empty       renaming (⊥ to Empty)  -- avoiding naming conflict with `⊥`
open import Relation.Nullary renaming (¬_ to neg)   -- avoiding naming conflict with `¬_`

consistency : neg ([] ⊢ ⊥)
consistency d with soundness d {λ _ → true}
... | ()


----------------
-- Exercise 9 --
----------------

{-
   Show that the boolean semantics also satisfies LEM.

   This lemma shows that:

   - while our natural deduction proof calculus is intuitionistic,
     then the boolean semantics we gave it is in fact classial; and

   - it is consistent and sound to extend intuitionistic propositional
     logic with classical reasoning principles such as LEM or DNE
-}

lem-soundness : {Δ : Hypotheses}
              → (φ : Formula)
              → {η : Env}
              → ⟦ Δ ⟧ₑ η ≤ ⟦ φ ∨ ¬ φ ⟧ η

lem-soundness {Δ} φ {η} with ⟦ φ ⟧ η       -- using LEM of the boolean semantics 
... | false = ≤-maximum (⟦ Δ ⟧ₑ η)
... | true  = ≤-maximum (⟦ Δ ⟧ₑ η)
