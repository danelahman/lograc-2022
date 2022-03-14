------------------------------------------------------------------------------------
-- Solutions to Week 4 exercises for the Logika v računalništvu course at UL FMF  --
-- Part 3 (Monads)                                                                --
--                                                                                --
-- Lecturer: Andrej Bauer                                                         --
-- Teaching Assistant: Danel Ahman                                                --
--                                                                                --
-- Course website: https://ucilnica.fmf.uni-lj.si/course/view.php?id=252          --
-- Lecture notes: http://www.andrej.com/zapiski/ISRM-LOGRAC-2022/                 --
------------------------------------------------------------------------------------

module Sol4.Monad where

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

open import Sol4.Monoid


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
    η         = λ x → ε , x ;
    _>>=_     = λ (m , x) f →
                   let (m' , y) = f x in
                   (m · m') , y ;
    η-left    = λ x f → cong (_, proj₂ (f x)) (ε-left (proj₁ (f x))) ;
    η-right   = λ (m , x) → cong (_, x) (ε-right m) ;
    >>=-assoc = λ (m , x) f g →
                   let (m' , y) = f x in
                   let (m'' , z) = g y in
                   cong (_, z) (·-assoc m m' m'') }


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
  write (m , x) m' = (m · m') , x

{-
   Prove that the `write` operation satisfies the equational theory
   corresponding to the writer monad.
-}

  write-ε : {X : Set l} → (k : T X) → write k ε ≡ k
        
  write-ε (m , x) =
    begin
      write (m , x) ε
    ≡⟨⟩
      (m · ε , x)
    ≡⟨ cong (_, x) (ε-right m) ⟩
      (m , x)
    ∎

  write-· : {X : Set l} → (k : T X) → (m m' : M)
          → write (write k m) m' ≡ write k (m · m')
 
  write-· (m , x) m' m'' =
    begin
      write (write (m , x) m') m''
    ≡⟨⟩
      (m · m' · m'' , x)
    ≡⟨ cong (_, x) (·-assoc m m' m'') ⟩
      (m · (m' · m'') , x)
    ≡⟨⟩
      write (m , x) (m' · m'')
    ∎


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
ToMonoid Mon = record {
  M       = T ⊤ ;
  ε       = η tt ;
  _·_     = λ m₁ m₂ → m₁ >>= (λ _ → m₂) ;
  ε-left  = λ m → η-left tt (λ _ → m) ;
  ε-right = λ m → η-right m ;
  ·-assoc = λ m₁ m₂ m₃ → >>=-assoc m₁ (λ _ → m₂) (λ _ → m₃) }

  where open Monad Mon

{-
   Note: The well-known fact is of course that monads are nothing but
   monoids in the category of endofunctors. The above solution has
   taken that monoid of endofunctors and instantiated it to `⊤`.
-}


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

record Action {l} (S : Set l) (Mon : Monoid {l}) : Set (lsuc l) where

  open Monoid Mon

  infixl 6 _↓_

  field
    -- action of `M` on `S` 
    _↓_ : S → M → S
    -- action laws
    ↓-ε : (s : S) → s ↓ ε ≡ s
    ↓-· : (s : S) → (m m' : M) → s ↓ m ↓ m' ≡ s ↓ m · m'


module _ {l} (S : Set l) (Mon : Monoid {l}) (Act : Action S Mon) where

  open Monoid Mon
  open Action Act

  Update : Monad {l}
  Update = record {
    T         = λ X     → S → M × X ;
    η         = λ x s   → ε , x  ;
    _>>=_     = _>>=-aux_ ;
    η-left    = λ x f   → fun-ext (η-left-aux x f) ;
    η-right   = λ f     → fun-ext (λ s → cong (_, proj₂ (f s)) (ε-right (proj₁ (f s)))) ;
    >>=-assoc = λ f g h → fun-ext (>>=-assoc f g h) }

      where

        _>>=-aux_ : {X Y : Set l} → (S → M × X) → (X → S → M × Y) → S → M × Y
        f >>=-aux g = λ s → let (m , x) = f s in
                            let (m' , y) = g x (s ↓ m) in
                            (m · m') , y

        η-left-aux : {X Y : Set l} (x : X) (f : X → S → M × Y) (s : S)
                   → (ε · proj₁ (f x (s ↓ ε)) , proj₂ (f x (s ↓ ε))) ≡ f x s
                   
        η-left-aux x f s rewrite (↓-ε s) = cong (_, proj₂ (f x s)) (ε-left (proj₁ (f x s)))

        >>=-assoc : {X Y Z : Set l} (f : S → M × X) (g : X → S → M × Y) (h : Y → S → M × Z) (s : S)
                  → ((f >>=-aux g) >>=-aux h) s ≡ (f >>=-aux (λ x → g x >>=-aux h)) s
        >>=-assoc f g h s =
          cong₂ _,_
            (begin
               proj₁ (f s) · proj₁ (g (proj₂ (f s)) (s ↓ proj₁ (f s))) ·
                 proj₁ (h (proj₂ (g (proj₂ (f s)) (s ↓ proj₁ (f s))))
                            (s ↓ proj₁ (f s) · proj₁ (g (proj₂ (f s)) (s ↓ proj₁ (f s)))))
             ≡⟨ ·-assoc _ _ _ ⟩
               proj₁ (f s) ·
                 (proj₁ (g (proj₂ (f s)) (s ↓ proj₁ (f s))) ·
                    proj₁ (h (proj₂ (g (proj₂ (f s)) (s ↓ proj₁ (f s))))
                               (s ↓ proj₁ (f s) · proj₁ (g (proj₂ (f s)) (s ↓ proj₁ (f s))))))
             ≡⟨ cong
                  (λ z → proj₁ (f s) · (proj₁ (g (proj₂ (f s)) (s ↓ proj₁ (f s))) ·
                                          proj₁ (h (proj₂ (g (proj₂ (f s)) (s ↓ proj₁ (f s)))) z)))
                  (sym (↓-· _ _ _)) ⟩
               proj₁ (f s) ·
                 (proj₁ (g (proj₂ (f s)) (s ↓ proj₁ (f s))) ·
                    proj₁ (h (proj₂ (g (proj₂ (f s)) (s ↓ proj₁ (f s))))
                               (s ↓ proj₁ (f s) ↓ proj₁ (g (proj₂ (f s)) (s ↓ proj₁ (f s))))))
             ∎)
            (begin
               proj₂ (h (proj₂ (g (proj₂ (f s)) (s ↓ proj₁ (f s))))
                          (s ↓ proj₁ (f s) · proj₁ (g (proj₂ (f s)) (s ↓ proj₁ (f s)))))
             ≡⟨ cong (λ z → proj₂ (h (proj₂ (g (proj₂ (f s)) (s ↓ proj₁ (f s)))) z)) (sym (↓-· _ _ _)) ⟩
               proj₂ (h (proj₂ (g (proj₂ (f s)) (s ↓ proj₁ (f s))))
                          (s ↓ proj₁ (f s) ↓ proj₁ (g (proj₂ (f s)) (s ↓ proj₁ (f s)))))
             ∎)
  
