module HOL where

-- Higher Order Logic
-- A Taste of Categorical Logic
-- Lars Birkedal & Aleˇs Bizjak
-- http://users-cs.au.dk/birke/modures/tutorial/categorical-logic-tutorial-notes.pdf
-- Agda version 2.4.2.2

open import Data.List
open import Data.Nat hiding (_*_)
open import Data.String hiding (_++_)
open import Data.Product
open import Data.Vec hiding (_++_; [_])

data type : Set where
  one : type
  prop : type
  nat : type
  _*_ : type → type → type
  _⇒_ : type → type → type

data variable : Set where
  var_name : String → variable

data function : ℕ → Set where
  fun_name : {n : ℕ} → String → function n

data term : Set where
  var : variable → term
  fun : {n : ℕ} → function n → Vec term n → term
  _∘_ : term → term → term -- Application
  Λ_∙_ : variable → term → term -- lambda
  π₁ : term → term
  π₂ : term → term
  _*_ : term → term → term
  <> : term
  ⊥ : term
  ⊤ : term
  _∧_ : term → term → term
  _∨_ : term → term → term
  _⇒_ : term → term → term
  for_all : variable → type → term → term
  exist : variable → type → term → term

postulate
  subst      : term → List (variable × term) → term

type-context = List (variable × type)

pattern _,_∶_ Γ x t = (x , t) ∷ Γ

module Rules (T : List type) (F : ∀ {n} → function n → List type) where

  data _⊢_∶_ : type-context → term → type → Set where

    -- Figure 1: Typing rules relative to a signature

    identity : {Γ : type-context} {x : variable} {t : type} →
               --TODO: Add C(type)
               -----------------------
               (Γ , x ∶ t) ⊢ var x ∶ t

    weakening : {Γ : type-context} {x : variable} {M : term} {s : type} {t : type} →

                (Γ ⊢ M ∶ t) →
                -------------------
                (Γ , x ∶ s) ⊢ M ∶ t

    app : {Γ : type-context} {M N : term} {t s : type} →

          (Γ ⊢ M ∶ (t ⇒ s)) →
          (Γ ⊢ N ∶ t) →
          ---------------
          (Γ ⊢ M ∘ N ∶ s)

    abs : {Γ : type-context} {x : variable} {M : term} {t s : type} →

          ((Γ , x ∶ t) ⊢ M ∶ s) →
          -------------------------
          (Γ ⊢ Λ x ∙ M ∶ (t ⇒ s))

    proj-1 : {Γ : type-context} {M : term} {t s : type} →

             (Γ ⊢ M ∶ (t * s)) →
             -----------------
             (Γ ⊢ π₁ M ∶ t)

    proj-2 : {Γ : type-context} {M : term} {t s : type} →

             (Γ ⊢ M ∶ (t * s)) →
             -----------------
             (Γ ⊢ π₂ M ∶ s)

    pairing : {Γ : type-context} {M N : term} {t s : type} →

              (Γ ⊢ M ∶ t) →
              (Γ ⊢ N ∶ s) →
              ------------------------
              (Γ ⊢ M * N ∶ (t * s)) 

    -- TODO: function symbol

    exchange : {Γ Δ : type-context} {x y : variable} {t t' s : type} {M : term} →
              -- TODO: Pattern
               ((Γ ++ [(x , t)] ++ [(y , t')] ++ Δ) ⊢ M ∶ s) →
               ---------------------------------------------------------------------------
               ((Γ ++ [(x , t')] ++ [(y , t)] ++ Δ) ⊢ (subst M ((y , var x) ∷ [(x , var y)])) ∶ s)

    contraction : {Γ : type-context} {x y : variable} {t s : type} {M : term} →

                  (((Γ , x ∶ t) , y ∶ t) ⊢ M ∶ s) →
                  -------------------------------------
                  ((Γ , x ∶ t) ⊢ subst M [(x , var y)] ∶ s)

    unit : {Γ : type-context} →
           --------------
           (Γ ⊢ <> ∶ one)

    -- Figure 2: Typing rules for logical connectives.

    false : {Γ : type-context} →
            --------------
            (Γ ⊢ ⊥ ∶ prop)

    true : {Γ : type-context} →
           --------------
           (Γ ⊢ ⊤ ∶ prop)

    conj : {Γ : type-context} {A B : term} →

           (Γ ⊢ A ∶ prop) →
           (Γ ⊢ B ∶ prop) →
           ------------------
           (Γ ⊢ A ∧ B ∶ prop)

    disj : {Γ : type-context} {A B : term} →

           (Γ ⊢ A ∶ prop) →
           (Γ ⊢ B ∶ prop) →
           ------------------
           (Γ ⊢ A ∨ B ∶ prop)

    impl : {Γ : type-context} {A B : term} →

           (Γ ⊢ A ∶ prop) →
           (Γ ⊢ B ∶ prop) →
           ------------------
           (Γ ⊢ A ⇒ B ∶ prop)

    for_all : {Γ : type-context} {x : variable} {t : type} {A : term} →

              ((Γ , x ∶ t) ⊢ A ∶ prop) →
              --------------------------
              (Γ ⊢ for_all x t A ∶ prop)

    exist : {Γ : type-context} {x : variable} {t : type} {A : term} →

            ((Γ , x ∶ t) ⊢ A ∶ prop) →
            --------------------------
            (Γ ⊢ exist x t A ∶ prop)

  term-context = List term

  postulate
    substTermContext : term-context → List (variable × term) → term-context

  data _∣_⊢_ : type-context → term-context → term → Set where

    -- Figure 3: Natural deduction rules for higher-order logic.

    identity : {Γ : type-context} {M : term} →

               (Γ ⊢ M ∶ prop) →
               ----------------
               (Γ ∣ [ M ] ⊢ M)

    cut : {Γ : type-context} {M N : term} {Δ₁ Δ₂ : term-context} →

          (Γ ∣ Δ₁ ⊢ M) →
          (Γ ∣ M ∷ Δ₂ ⊢ N) →
          ------------------
          (Γ ∣ Δ₁ ++ Δ₂ ⊢ N)

    weak-prop : {Γ : type-context} {M N : term} {Δ : term-context} →

                (Γ ∣ Δ ⊢ M) →
                (Γ ⊢ N ∶ prop) →
                ----------------
                (Γ ∣ N ∷ Δ ⊢ M)

    contr-prop : {Γ : type-context} {M N : term} {Δ : term-context} →

                 (Γ ∣ N ∷ N ∷ Δ ⊢ M) →
                 ---------------------
                 (Γ ∣ N ∷ Δ ⊢ M)

    exch-prop : {Γ : type-context} {M N L : term} {Δ₁ Δ₂ : term-context} →

                (Γ ∣ Δ₁ ++ [ M ] ++ [ N ] ++ Δ₂ ⊢ L) →
                --------------------------------------
                (Γ ∣ Δ₁ ++ [ N ] ++ [ M ] ++ Δ₂ ⊢ L)

    weak-type : {Γ : type-context} {x : variable} {t : type} {M : term} {Δ : term-context} →

                (Γ ∣ Δ ⊢ M) →
                ---------------------
                ((Γ , x ∶ t) ∣ Δ ⊢ M)

    contr-type : {Γ : type-context} {x y : variable} {t : type} {Ω : term-context} {M : term} →

                 ((Γ ++ [ x , t ] ++ [ y , t ]) ∣ Ω ⊢ M) →
                 ----------------------------------------------------------------------
                 ((Γ , x ∶ t) ∣ substTermContext Ω [ x , var y ] ⊢ subst M [ x , var y ])

    exch-type : {Γ Δ : type-context} {Ω : term-context} {M : term} {x y : variable} {t s : type} →

                ( (Γ ++ [ x , t ] ++ [ y , s ] ++ Δ) ∣ Ω ⊢ M ) →
                ----------------------------------------------
                ( (Γ ++ [ y , s ] ++ [ x , t ] ++ Δ) ∣ Ω ⊢ M )

    substitution : {Δ₁ Δ₂ Γ : type-context} {Ω : term-context} {M N : term} {t : type} {x : variable} →

                   (Γ ⊢ M ∶ t) →
                   ((Δ₁ ++ [ x , t ] ++ Δ₂) ∣ Ω ⊢ N) →
                   --------------------------------------------------------------------
                   ((Δ₁ ++ Γ ++ Δ₂) ∣ substTermContext Ω [ x , M ] ⊢ subst N [ x , M ])

  --  true
  --  false
  --  and-I
  --  and-E1
  --  and-E2
  --  or-I1
  --  or-I2
  --  or-E
  --  imp-I
  --  imp-E
  --  forall-E
  --  forall-I
  --  exist-E
  --  exist-I
