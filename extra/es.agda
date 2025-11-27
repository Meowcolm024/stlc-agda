module extra.es where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Relation.Nullary.Negation using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)

infixr 7 _⇒_

data Type : Set where
  `ℕ  : Type
  _⇒_ : Type → Type → Type

infixl 5 _,-_

data Context : Set where
  ∅    : Context
  _,-_ : Context → Type → Context

variable
  A B C : Type
  Γ Δ Σ : Context

infix  4 _⊢_
infix  5 ƛ_
infixl 7 _·_
infixl 9 _[_]

data Subst : Context → Context → Set

data _⊢_ : Context → Type → Set where
  ⋆ :
      -----------
      Γ ,- A ⊢ A

  ƛ_ :
      (M : Γ ,- A ⊢ B)
    → -----------------
      Γ ⊢ A ⇒ B
      
  _·_ :
      (M : Γ ⊢ A ⇒ B)
      (N : Γ ⊢ A)
    → ----------------
      Γ ⊢ B

  _[_] :
      (M : Γ ⊢ A)
      (σ : Subst Γ Δ)
    → ----------------
      Δ ⊢ A

variable
  L M N L' M' N' : Γ ⊢ A
  σ τ υ : Subst Γ Δ

infixr 6 _•_
infixr 5 _⨟_

data Subst where
  id :
      ----------
      Subst Γ Γ

  ↑ :
      -----------------
      Subst Γ (Γ ,- A)

  _•_ :
      (M : Δ ⊢ A)
      (σ : Subst Γ Δ)
    → -----------------
      Subst (Γ ,- A) Δ

  _⨟_ :
      (σ : Subst Γ Δ)
      (τ : Subst Δ Σ)
    → ----------------
      Subst Γ Σ

-- a sequence of shifts
data Shifts : Subst Γ Δ → Set where
  S-↑ : Shifts {Γ} {Γ ,- A} ↑
  S-⨟ : Shifts σ → Shifts (↑ ⨟ σ)

-- the basic rewriting system
module basic where
  data σNf : Γ ⊢ A → Set where
    σNf-⋆ : σNf {Γ ,- A} ⋆
    σNf-↑ : Shifts σ → σNf (⋆ [ σ ])
    σNf-· : σNf M → σNf N → σNf (M · N)
    σNf-ƛ : σNf M → σNf (ƛ M)

  data σNf-Subst : Subst Γ Δ → Set where
    σNf-si : σNf-Subst {Γ} id
    σNf-su : σNf-Subst {Γ} {Γ ,- A} ↑
    σNf-sc : σNf-Subst σ → σNf-Subst (M • σ)

  infix  2 _—→_ _~→_

  data _~→_ : Subst Γ Δ → Subst Γ Δ → Set where
    id⨟ :
        ------------
        id ⨟ σ ~→ σ

    ↑⨟id :
         -----------------------
         ↑ ⨟ (id {Γ ,- A}) ~→ ↑

    ↑⨟• :
        -----------------
        ↑ ⨟ (M • σ) ~→ σ

    •⨟ :
       ---------------------------------
       (M • σ) ⨟ τ ~→ M [ τ ] • (σ ⨟ τ)

    ⨟⨟ :
       ---------------------------
       (σ ⨟ τ) ⨟ υ ~→ σ ⨟ (τ ⨟ υ)

  data _—→_ : Γ ⊢ A → Γ ⊢ A → Set where
    β-ƛ :
        (VM : σNf M)
        → --------------------------
        (ƛ M) · N —→ M [ N • id ]

    σ-⋆ :
        -------------------------
        ⋆ [ (id {Γ ,- A}) ] —→ ⋆

    σ-• :
        -----------------
        ⋆ [ M • σ ] —→ M

    σ-· :
        -----------------------------------
        (M · N) [ σ ] —→ M [ σ ] · N [ σ ]

    σ-ƛ :
        -----------------------------------
        (ƛ M) [ σ ] —→ ƛ M [ ⋆ • (σ ⨟ ↑) ]

    σ-⨟ :
        -----------------------------
        M [ σ ] [ τ ] —→ M [ σ ⨟ τ ]

  open import Relation.Binary.Construct.Closure.ReflexiveTransitive
    using (Star; ε; _◅_; _◅◅_)

  -- multistep
  _—↠_ : (M N : Γ ⊢ A) → Set
  M —↠ N = Star _—→_ M N

  -- confluence of the basic rewriting system
  confluence : L —↠ M → L —↠ M' → ∃[ N ] (M —↠ N) × (M' —↠ N)
  confluence ε                L—↠M'               = _ , L—↠M' , ε
  confluence L—→M             ε                   = _ , ε , L—→M
  confluence (β-ƛ VM ◅ L₁—↠M) (β-ƛ VM₁ ◅ L₁'—↠M') = confluence L₁—↠M L₁'—↠M'
  confluence (σ-⋆ ◅ L₁—↠M)    (σ-⋆ ◅ L₁'—↠M')     = confluence L₁—↠M L₁'—↠M'
  confluence (σ-• ◅ L₁—↠M)    (σ-• ◅ L₁'—↠M')     = confluence L₁—↠M L₁'—↠M'
  confluence (σ-· ◅ L₁—↠M)    (σ-· ◅ L₁'—↠M')     = confluence L₁—↠M L₁'—↠M'
  confluence (σ-ƛ ◅ L₁—↠M)    (σ-ƛ ◅ L₁'—↠M')     = confluence L₁—↠M L₁'—↠M'
  confluence (σ-⨟ ◅ L₁—↠M)    (σ-⨟ ◅ L₁'—↠M')     = confluence L₁—↠M L₁'—↠M'
 
