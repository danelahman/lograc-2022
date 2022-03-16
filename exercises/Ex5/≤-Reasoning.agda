---------------------------------------------------------------------------
-- Week 5 exercises for the Logika v računalništvu course at UL FMF      --
-- Inequational reasoning machinery for the `≤` relation on booleans     --
--                                                                       --
-- Lecturer: Andrej Bauer                                                --
-- Teaching Assistant: Danel Ahman                                       --
--                                                                       --
-- Course website: https://ucilnica.fmf.uni-lj.si/course/view.php?id=252 --
-- Lecture notes: http://www.andrej.com/zapiski/ISRM-LOGRAC-2022/        --
---------------------------------------------------------------------------

module Ex5.≤-Reasoning where

open import Data.Bool renaming (_∧_ to _and_; _∨_ to _or_)
open import Data.Bool.Properties

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

infix  3 _∎ᵇ
infixr 2 _≤⟨⟩_ step-≤ step-≡ᵇ
infix  1 beginᵇ_

------------------------------------------------------------------------
-- Equality implies inequality

≤-≡ : {x y : Bool} → x ≡ y → x ≤ y
≤-≡ refl = b≤b

------------------------------------------------------------------------
-- Inequational reasoning

beginᵇ_ : ∀{x y : Bool} → x ≤ y → x ≤ y
beginᵇ_ x≤y = x≤y

_≤⟨⟩_ : ∀ (x {y} : Bool) → x ≤ y → x ≤ y
_ ≤⟨⟩ x≤y = x≤y

step-≤ : ∀ (x {y z} : Bool) → y ≤ z → x ≤ y → x ≤ z
step-≤ _ y≤z x≤y = ≤-trans x≤y y≤z

step-≡ᵇ : ∀ (x {y z} : Bool) → y ≤ z → x ≡ y → x ≤ z
step-≡ᵇ _ y≤z refl = y≤z

_∎ᵇ : ∀ (x : Bool) → x ≤ x
_∎ᵇ _ = ≤-refl

syntax step-≤  x y≤z x≤y = x ≤⟨ x≤y ⟩ y≤z
syntax step-≡ᵇ x y≤z x≡y = x ≡ᵇ⟨ x≡y ⟩ y≤z
