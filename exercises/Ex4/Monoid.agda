---------------------------------------------------------------------------
-- Week 4 exercises for the Logika v računalništvu course at UL FMF      --
-- Part 2 (Monoids)                                                      --
--                                                                       --
-- Lecturer: Andrej Bauer                                                --
-- Teaching Assistant: Danel Ahman                                       --
--                                                                       --
-- Course website: https://ucilnica.fmf.uni-lj.si/course/view.php?id=252 --
-- Lecture notes: http://www.andrej.com/zapiski/ISRM-LOGRAC-2022/        --
---------------------------------------------------------------------------

{-
   NOTE: Uncomment the pragma below if you start working on
   `Ex4.Monad` before filling all the holes in this module.
-}

-- {-# OPTIONS --allow-unsolved-metas #-}

{-
   This week's exercises are split between multiple modules.
   Solve them in the following order:

   1. `Dictionary.agda`
   2. `Monoid.agda`
   3. `Monad.agda`

   Attempt the bonus exercises only when you have finished all the
   numbered exercises.
-}

module Ex4.Monoid where

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


----------------------------------
-- Monoids and Monoid Morphisms --
----------------------------------

{-
   First, recall the type of monoids from the lecture.
-}

record Monoid {l} : Set (lsuc l) where
  infixl 7 _·_
  field
    -- carrier type of the monoid
    M       : Set l
    -- identity element (unicode with `\epsilon`)
    ε       : M
    -- binary operation (unicode with `\cdot`)
    _·_     : M → M → M
    -- monoid laws
    ε-left  : (m : M) → ε · m ≡ m
    ε-right : (m : M) → m · ε ≡ m
    ·-assoc : (m₁ m₂ m₃ : M) → (m₁ · m₂) · m₃ ≡ m₁ · (m₂ · m₃)

{-
   Second, recall the type of monoid morphisms from the lecture.
-}

infixl 6 _→ᴹ_ -- unicode with `\to\^M`

record _→ᴹ_ {l} (Mon₁ Mon₂ : Monoid {l}) : Set l where
  open Monoid Mon₁ renaming (M to M₁; ε to ε₁; _·_ to _·₁_; ε-left to ε-left₁; 
                             ε-right to ε-right₁; ·-assoc to ·-assoc₁)
  open Monoid Mon₂ renaming (M to M₂; ε to ε₂; _·_ to _·₂_; ε-left to ε-left₂; 
                             ε-right to ε-right₂; ·-assoc to ·-assoc₂)
  field
    -- map between the carriers of the monoids
    map   : M₁ → M₂
    -- map preserves identity element and the binary operation
    map-ε : map ε₁ ≡ ε₂
    map-· : (m₁ m₁' : M₁) → map (m₁ ·₁ m₁') ≡ map m₁ ·₂ map m₁'

{-
   Third, recall the equality between monoid morphisms. Note that
   it was defined only in terms of the `map` components of `→ᴹ`.

   See the Bonus Monoid Morphisms Exercise for relating `≡ᴹ` to `≡`.
-}
   
infixl 5 _≡ᴹ_ -- unicode with `\equiv\^M`

_≡ᴹ_ : ∀ {l} {Mon₁ Mon₂ : Monoid {l}} → Mon₁ →ᴹ Mon₂ → Mon₁ →ᴹ Mon₂ → Set l
f ≡ᴹ g = map₁ ≡ map₂

  where open _→ᴹ_ f renaming (map to map₁)
        open _→ᴹ_ g renaming (map to map₂)

{-
   Fourth, recall the identity and composition for monoid morphisms.
-}

idᴹ : ∀ {l} {Mon : Monoid {l}} → Mon →ᴹ Mon
idᴹ = record {
  map   = id ;
  map-ε = refl ;
  map-· = λ _ _ → refl }

_∘ᴹ_ : ∀ {l} {Mon₁ Mon₂ Mon₃ : Monoid {l}} → Mon₂ →ᴹ Mon₃ → Mon₁ →ᴹ Mon₂ → Mon₁ →ᴹ Mon₃ -- unicode with `\circ\^M`
g ∘ᴹ f = record {
  map   = map₂ ∘ map₁ ;
  map-ε = trans (cong map₂ map-ε₁) map-ε₂ ;
  map-· = λ m₁ m₁' → trans (cong map₂ (map-·₁ m₁ m₁')) (map-·₂ (map₁ m₁) (map₁ m₁')) }

  where open _→ᴹ_ f renaming (map to map₁; map-ε to map-ε₁; map-· to map-·₁)
        open _→ᴹ_ g renaming (map to map₂; map-ε to map-ε₂; map-· to map-·₂)


----------------
-- Exercise 4 --
----------------

{-
   Define the product structure on two monoids.
-}

infixl 7 _×ᴹ_

_×ᴹ_ : ∀ {l} → Monoid {l} → Monoid {l} → Monoid {l}
Mon₁ ×ᴹ Mon₂ = {!!}

{-
   Prove that your definition of `×ᴹ` is indeed the Cartesian product
   of two monoids (in the category of monoids):
   
   - define the projection and pairing monoid morphisms,
   - prove that they satisfy the expected (beta-)laws, and
   - show that the latter is a unique such (the eta-law).
-}

fst : ∀ {l} {Mon₁ Mon₂ : Monoid {l}} → Mon₁ ×ᴹ Mon₂ →ᴹ Mon₁
fst {l} {Mon₁} {Mon₂} = {!!}

snd : ∀ {l} {Mon₁ Mon₂ : Monoid {l}} → Mon₁ ×ᴹ Mon₂ →ᴹ Mon₂
snd {l} {Mon₁} {Mon₂} = {!!}

⟨_,_⟩ : ∀ {l} {Mon₁ Mon₂ Mon₃ : Monoid {l}}
      → Mon₁ →ᴹ Mon₂ → Mon₁ →ᴹ Mon₃ → Mon₁ →ᴹ Mon₂ ×ᴹ Mon₃
      
⟨ f , g ⟩ = {!!}

fst∘⟨,⟩ : ∀ {l} {Mon₁ Mon₂ Mon₃ : Monoid {l}}
        → {f : Mon₁ →ᴹ Mon₂} {g : Mon₁ →ᴹ Mon₃}
        → (fst ∘ᴹ ⟨ f , g ⟩) ≡ᴹ f
        
fst∘⟨,⟩ = {!!}

snd∘⟨,⟩ : ∀ {l} {Mon₁ Mon₂ Mon₃ : Monoid {l}}
        → {f : Mon₁ →ᴹ Mon₂} {g : Mon₁ →ᴹ Mon₃}
        → (snd ∘ᴹ ⟨ f , g ⟩) ≡ᴹ g
        
snd∘⟨,⟩ = {!!}

⟨,⟩-unique : ∀ {l} {Mon₁ Mon₂ Mon₃ : Monoid {l}}
           → {f : Mon₁ →ᴹ Mon₂} {g : Mon₁ →ᴹ Mon₃}
           → {h : Mon₁ →ᴹ Mon₂ ×ᴹ Mon₃}
           → (fst ∘ᴹ h) ≡ᴹ f
           → (snd ∘ᴹ h) ≡ᴹ g
           → h ≡ᴹ ⟨ f , g ⟩
           
⟨,⟩-unique p q = {!!}


-------------------------------------
-- Bonus Monoid Morphisms Exercise --
-------------------------------------

{-
   When used with the default settings, Agda supports the axiom K of
   type theory (https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29).

   Having axiom K in hand, we can then easily define the uniqueness of
   identity proofs (UIP) principle, which states that every two proofs
   `p q : x ≡ y` are themselves propositionally equal, i.e., `p ≡ q`.

   Of course, if you are to use Agda to formalise topics in Homotopy
   Type Theory or higher categories, you will want to turn axiom K off,
   which you can do with the `--without-K` option/pragma, e.g., see
   https://agda.readthedocs.io/en/v2.6.2.1/language/without-k.html.
-}

uip : ∀ {l} {A : Set l} {x y : A} → (p q : x ≡ y) → p ≡ q
uip refl refl = refl

{-
   Using `uip`, prove the extensionality principle for the equalities
   between monoid morphisms. Intuitively, `→ᴹ-ext` says that for two
   monoid morphisms to be equal, it suffices if only their carrier
   maps are equal (which is exactly how we defined `≡ᴹ` above).
-}

→ᴹ-ext :  ∀ {l} {Mon₁ Mon₂ : Monoid {l}} {f g : Mon₁ →ᴹ Mon₂} → f ≡ᴹ g → f ≡ g
→ᴹ-ext = {!!}
