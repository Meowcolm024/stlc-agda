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

infix 4 _∋_

data _∋_ : Context → Type → Set where
  Z : Γ ,- A ∋ A
  S : Γ ∋ A → Γ ,- B ∋ A

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
  L M N : Γ ⊢ A
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

data Shifts : Subst Γ Δ → Set where
  S-↑ : Shifts {Γ} {Γ ,- A} ↑
  S-⨟ : Shifts σ → Shifts (↑ ⨟ σ)

data NormSubst : Subst Γ Δ → Set where
  NS-I  : Shifts σ → NormSubst σ
  NS-id : NormSubst {Γ} id
  NS-•  : NormSubst (M • σ)

data Normal : Γ ⊢ A → Set

data Neutral : Γ ⊢ A → Set where
  I-⋆ : Neutral {Γ ,- A} ⋆
  I-↑ : Shifts σ → Neutral (⋆ [ σ ])
  I-· : Neutral M → Normal N → Neutral (M · N)

data Normal where
  V-I : Neutral M → Normal M
  V-ƛ : Normal M → Normal (ƛ M)

-- normal order reduction

infix  2 _—→_ _~→_

data _~→_ : Subst Γ Δ → Subst Γ Δ → Set

data _—→_ : Γ ⊢ A → Γ ⊢ A → Set where
  ξ-ƛ :
      (M—→N : M —→ N)
    → ----------------
      ƛ M —→ ƛ N

  β-ƛ :
      (VM : Normal M)
    → --------------------------
      (ƛ M) · N —→ M [ N • id ]

  ξ-· :
      (L—→M : L —→ M)
    → ----------------
      L · N —→ M · N

  ξ-I :
      (IL : Neutral L)
      (M—→N : M —→ N)
    → -----------------
      L · M —→ L · N

  σ-Z :
      -------------------------
      ⋆ [ (id {Γ ,- A}) ] —→ ⋆

  σ-M :
      -----------------
      ⋆ [ M • σ ] —→ M

  σ-ξ :
      σ ~→ τ
    → -------------------
      ⋆ [ σ ] —→ ⋆ [ τ ]

  σ-· :
      -----------------------------------
      (M · N) [ σ ] —→ M [ σ ] · N [ σ ]

  σ-ƛ :
      -----------------------------------
      (ƛ M) [ σ ] —→ ƛ M [ ⋆ • (σ ⨟ ↑) ]

  σ-⨟ :
      -----------------------------
      M [ σ ] [ τ ] —→ M [ σ ⨟ τ ]

data _~→_ where
  id⨟ :
      ------------
      id ⨟ σ ~→ σ

  ↑⨟id :
      -----------------------
      ↑ ⨟ (id {Γ ,- A}) ~→ ↑

  ↑⨟• :
      -----------------
      ↑ ⨟ (M • σ) ~→ σ

  ↑⨟ :
      (σ~→τ : σ ~→ τ)
    → ----------------
      ↑ ⨟ σ ~→ ↑ ⨟ τ

  •⨟ :
      ---------------------------------
      (M • σ) ⨟ τ ~→ M [ τ ] • (σ ⨟ τ)

  ⨟⨟ :
      ---------------------------
      (σ ⨟ τ) ⨟ υ ~→ σ ⨟ (τ ⨟ υ)

Shifts-¬~→ : Shifts σ → ¬ (σ ~→ τ)
Shifts-¬~→ (S-⨟ x) (↑⨟ σ~→τ) = Shifts-¬~→ x σ~→τ

NormSubst-¬~→ : NormSubst σ → ¬ (σ ~→ τ)
NormSubst-¬~→ (NS-I x) σ~→τ = Shifts-¬~→ x σ~→τ

subst-prog : (σ : Subst Γ Δ) → NormSubst σ ⊎ ∃[ τ ] (σ ~→ τ)
subst-prog id                          = inj₁ NS-id
subst-prog ↑                           = inj₁ (NS-I S-↑)
subst-prog (M • σ)                     = inj₁ NS-•
subst-prog (id ⨟ σ')                   = inj₂ (σ' , id⨟)
subst-prog (↑ ⨟ σ') with subst-prog σ'
... | inj₁ (NS-I x)                    = inj₁ (NS-I (S-⨟ x))
... | inj₁ NS-id                       = inj₂ (↑ , ↑⨟id)
... | inj₁ (NS-• {σ = σ})              = inj₂ (σ , ↑⨟•)
... | inj₂ (τ' , σ'~→τ')               = inj₂ (↑ ⨟ τ' , ↑⨟ σ'~→τ')
subst-prog (M • σ ⨟ σ')                = inj₂ (M [ σ' ] • (σ ⨟ σ') , •⨟)
subst-prog ((σ ⨟ σ₁) ⨟ σ')             = inj₂ (σ ⨟ σ₁ ⨟ σ' , ⨟⨟)

Normal-¬—→  : Normal M → ¬ (M —→ N)
Neutral-¬—→ : Neutral M → ¬ (M —→ N)

Neutral-¬—→ (I-↑ x)     (σ-ξ σ~→τ)   = Shifts-¬~→ x σ~→τ
Neutral-¬—→ (I-· IM VM) (ξ-· M—→N)   = Neutral-¬—→ IM M—→N
Neutral-¬—→ (I-· IM VM) (ξ-I _ M—→N) = Normal-¬—→ VM M—→N

Normal-¬—→ (V-I IM) M—→N       = Neutral-¬—→ IM M—→N
Normal-¬—→ (V-ƛ VM) (ξ-ƛ M—→N) = Normal-¬—→ VM M—→N

progress : (M : Γ ⊢ A) → Normal M ⊎ ∃[ N ] (M —→ N)
progress ⋆                           = inj₁ (V-I I-⋆)
progress (ƛ M) with progress M
... | inj₁ VM                        = inj₁ (V-ƛ VM)
... | inj₂ (N , M—→N)                = inj₂ (ƛ N , ξ-ƛ M—→N)
progress (M · M') with progress M
... | inj₂ (N , M—→N)                = inj₂ (N · M' , ξ-· M—→N)
... | inj₁ (V-ƛ {M = M₁} VM)         = inj₂ (M₁ [ M' • id ] , β-ƛ VM)
... | inj₁ (V-I IM) with progress M'
...   | inj₁ VM'                     = inj₁ (V-I (I-· IM VM'))
...   | inj₂ (N' , M'—→N')           = inj₂ (M · N' , ξ-I IM M'—→N')
progress (⋆ [ σ ]) with subst-prog σ
... | inj₁ (NS-I x)                  = inj₁ (V-I (I-↑ x))
... | inj₁ NS-id                     = inj₂ (⋆ , σ-Z)
... | inj₁ (NS-• {M = M})            = inj₂ (M , σ-M)
... | inj₂ (τ , σ~→τ)                = inj₂ (⋆ [ τ ] , σ-ξ σ~→τ)
progress ((ƛ M) [ σ ])               = inj₂ (ƛ M [ ⋆ • (σ ⨟ ↑) ] , σ-ƛ)
progress ((M · M') [ σ ])            = inj₂ (M [ σ ] · M' [ σ ] , σ-·)
progress (M [ σ ] [ σ' ])            = inj₂ (M [ σ ⨟ σ' ] , σ-⨟)

~→-determ : σ ~→ τ → σ ~→ υ → τ ≡ υ
~→-determ id⨟       id⨟       = refl
~→-determ ↑⨟id      ↑⨟id      = refl
~→-determ ↑⨟•       ↑⨟•       = refl
~→-determ (↑⨟ σ~→τ) (↑⨟ σ~→υ) rewrite ~→-determ σ~→τ σ~→υ = refl
~→-determ •⨟        •⨟        = refl
~→-determ ⨟⨟        ⨟⨟        = refl

—→-determ : L —→ M → L —→ N → M ≡ N
—→-determ (ξ-ƛ L—→M)    (ξ-ƛ L—→N)    rewrite —→-determ L—→M L—→N = refl
—→-determ (β-ƛ VM)      (β-ƛ _)       = refl
—→-determ (β-ƛ VM)      (ξ-· L—→N)    = ⊥-elim (Normal-¬—→ (V-ƛ VM) L—→N)
—→-determ (ξ-· L—→M)    (β-ƛ VM)      = ⊥-elim (Normal-¬—→ (V-ƛ VM) L—→M)
—→-determ (ξ-· L—→M)    (ξ-· L—→N)    rewrite —→-determ L—→M L—→N = refl
—→-determ (ξ-· L—→M)    (ξ-I VM L—→N) = ⊥-elim (Neutral-¬—→ VM L—→M)
—→-determ (ξ-I VM L—→M) (ξ-· L—→N)    = ⊥-elim (Neutral-¬—→ VM L—→N)
—→-determ (ξ-I VM L—→M) (ξ-I _ L—→N)  rewrite —→-determ L—→M L—→N = refl
—→-determ σ-Z           σ-Z           = refl
—→-determ σ-M           σ-M           = refl
—→-determ (σ-ξ σ~→τ)    (σ-ξ σ~→υ)    rewrite ~→-determ σ~→τ σ~→υ = refl
—→-determ σ-·           σ-·           = refl
—→-determ σ-ƛ           σ-ƛ           = refl
—→-determ σ-⨟           σ-⨟           = refl

-- note: determism implies confluence
