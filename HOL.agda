module HOL where

-- Higher Order Logic
-- A Taste of Categorical Logic
-- Lars Birkedal & Aleˇs Bizjak
-- Agda version: Agda version 2.4.2.2

open import Data.List
open import Data.String
open import Data.Product
  
data type : Set where
  one : type
  prop : type
  nat : type
  _*_ : type → type → type
  _⇒_ : type → type → type

data variable : Set where
  var_name : String → variable

data term : Set where
  var : variable → term
  _∘_ : term → term → term -- Application
  Λ_∙_ : variable → term → term -- lambda
  π₁ : term → term
  π₂ : term → term
  _*_ : term → term → term
  ⊥ : term
  ⊤ : term
  _∧_ : term → term → term
  _∨_ : term → term → term
  _⇒_ : term → term → term
  for_all : variable → type → term → term
  exist : variable → type → term → term

type-context = List (variable × type)

pattern _,_∶_ Γ x t = (x , t) ∷ Γ

data _⊢_∶_ : type-context → term → type → Set where

  identity : {Γ : type-context} {x : variable} {t : type} →
             --TODO: Add C(type)
             -------------------
             (Γ , x ∶ t) ⊢ var x ∶ t

  weakening : {Γ : type-context} {x : variable} {M : term} {s : type} {t : type} →

              (Γ ⊢ M ∶ t) →
              -----------------------
              (Γ , x ∶ s) ⊢ M ∶ t

  app : {Γ : type-context} {M N : term} {t s : type} →

        (Γ ⊢ M ∶ (t ⇒ s)) →
        (Γ ⊢ N ∶ t) →
        -----------------
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
  -- TODO: exchange
  -- TODO: contradiction
  
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
         --
         (Γ ⊢ A ∨ B ∶ prop)

  impl : {Γ : type-context} {A B : term} →

         (Γ ⊢ A ∶ prop) →
         (Γ ⊢ B ∶ prop) →
         ------------------
         (Γ ⊢ A ⇒ B ∶ prop)

  for_all : {Γ : type-context} {x : variable} {t : type} {A : term} →

            ((Γ , x ∶ t) ⊢ A ∶ prop) →
            ------------------------------
            (Γ ⊢ for_all x t A ∶ prop)

  exist : {Γ : type-context} {x : variable} {t : type} {A : term} →

          ((Γ , x ∶ t) ⊢ A ∶ prop) →
          ------------------------------
          (Γ ⊢ exist x t A ∶ prop)
