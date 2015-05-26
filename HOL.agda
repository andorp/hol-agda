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
  fun_name : (n : ℕ) → String → function n

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
  subst : term → List (variable × variable) → term

type-context = List (variable × type)

pattern _,_∶_ Γ x t = (x , t) ∷ Γ

data _⊢_∶_ : type-context → term → type → Set where

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
             ((Γ ++ [(x , t')] ++ [(y , t)] ++ Δ) ⊢ (subst M ((y , x) ∷ [(x , y)])) ∶ s)

  contraction : {Γ : type-context} {x y : variable} {t s : type} {M : term} →

                (((Γ , x ∶ t) , y ∶ t) ⊢ M ∶ s) →
                -------------------------------------
                ((Γ , x ∶ t) ⊢ subst M [(x , y)] ∶ s)

  unit : {Γ : type-context} →
         --------------
         (Γ ⊢ <> ∶ one)
  
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
