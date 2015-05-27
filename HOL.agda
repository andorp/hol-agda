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
open import Relation.Binary.PropositionalEquality using (_≡_)

data function : ℕ → Set where
  fun_name : {n : ℕ} → String → function n

data variable : Set where
  var_name : String → variable

module Syntax {type₁ : Set} (types : List type₁) (funs : ∀ {n} → function n → Vec type₁ n) where

  data type : Set where
    one : type
    prop : type
    typ : type₁ → type
    _*_ : type → type → type
    _⇒_ : type → type → type

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

  data Any {A : Set} (P : A → Set) : List A → Set where
    zero : ∀ {x xs} (p : P x) → Any P (x ∷ xs)
    suc  : ∀ {x xs} (a : Any P xs) → Any P (x ∷ xs)

  _⋿_ : ∀ {A : Set} → A → List A → Set
  x ⋿ xs = Any (_≡_ x) xs

  data _⊢_∶_ : type-context → term → type → Set where

    -- Figure 1: Typing rules relative to a signature (T, F). Γ is a type context, i.e., a list
    -- x1 : σ1, x2 : σ2, . . . , xn : σn and when we write Γ, x : σ we assume that x does not occur in Γ .

    identity : {Γ : type-context} {x : variable} {t : type₁} →

               (t ⋿ types) →
               -----------------------
               (Γ , x ∶ typ t) ⊢ var x ∶ typ t

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

    -- Figure 2: Typing rules for logical connectives. Note that these are not introduction and elimination
    -- rules for connectives. These merely state that some things are propositions, i.e., of type
    -- Prop

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

    -- Figure 3: Natural deduction rules for higher-order logic. Note that by convention x does not
    -- appear free in Θ, Ξ or ψ in the rules ∀-I and ∃-E since we implicitly have that x is not in Γ and
    -- Θ, Ξ and ψ are well formed in context Γ .

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

    true : {Γ : type-context} {Ω : term-context} →
           ---------
           Γ ∣ Ω ⊢ ⊤

    false : {Γ : type-context} {Ω : term-context} →
            ---------
            Γ ∣ Ω ⊢ ⊥

    and-I : {Γ : type-context} {Ω : term-context} {M N : term} →

            (Γ ∣ Ω ⊢ N) →
            (Γ ∣ Ω ⊢ M) →
            -----------------
            (Γ ∣ Ω ⊢ (M ∧ N))

    and-E1 : {Γ : type-context} {Ω : term-context} {M N : term} →

             (Γ ∣ Ω ⊢ (M ∧ N)) →
             -----------------
             (Γ ∣ Ω ⊢ M)

    and-E2 : {Γ : type-context} {Ω : term-context} {M N : term} →

             (Γ ∣ Ω ⊢ (M ∧ N)) →
             -----------------
             (Γ ∣ Ω ⊢ N)

    or-I1 : {Γ : type-context} {Ω : term-context} {M N : term} →

            (Γ ∣ Ω ⊢ M) →
            -----------------
            (Γ ∣ Ω ⊢ (N ∨ M))

    or-I2 : {Γ : type-context} {Ω : term-context} {M N : term} →

            (Γ ∣ Ω ⊢ M) →
            -----------------
            (Γ ∣ Ω ⊢ (M ∨ N))

    or-E : {Γ : type-context} {Ω : term-context} {L M N : term} →

           (Γ ∣ M ∷ Ω ⊢ L) →
           (Γ ∣ N ∷ Ω ⊢ L) →
           ---------------------
           (Γ ∣ (M ∨ N) ∷ Ω ⊢ L)

    imp-I : {Γ : type-context} {Ω : term-context} {M N : term} →

            (Γ ∣ M ∷ Ω ⊢ N) →
            -----------------
            (Γ ∣ Ω ⊢ (M ⇒ N))

    imp-E : {Γ : type-context} {Ω : term-context} {M N : term} →

            (Γ ∣ Ω ⊢ (M ⇒ N)) →
            (Γ ∣ Ω ⊢ M) →
            -----------------
            (Γ ∣ Ω ⊢ N)

    forall-I : {Γ : type-context} {Ω : term-context} {x : variable} {t : type} {N : term} →

               ((Γ , x ∶ t) ∣ Ω ⊢ N) →
               -----------------------
               (Γ ∣ Ω ⊢ for_all x t N)

    forall-E : {Γ : type-context} {Ω : term-context} {x : variable} {t : type} {M N : term} →

               (Γ ⊢ M ∶ t) →
               (Γ ∣ Ω ⊢ for_all x t N) →
               ---------------------------
               (Γ ∣ Ω ⊢ subst N [ x , M ])

    exist-I : {Γ : type-context} {Ω : term-context} {x : variable} {t : type} {M N : term} →

              (Γ ⊢ M ∶ t) →
              (Γ ∣ Ω ⊢ subst N [ x , M ]) →
              ---------------------
              (Γ ∣ Ω ⊢ exist x t N)

    exist-E : {Γ : type-context} {Ω₁ Ω₂ : term-context} {x : variable} {t : type} {M N : term} →

              (Γ ∣ Ω₁ ⊢ exist x t N) →
              ((Γ , x ∶ t) ∣ N ∷ Ω₂ ⊢ M) →
              ----------------------------
              (Γ ∣ Ω₁ ++ Ω₂ ⊢ M)
