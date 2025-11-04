module stlc.clos where

open import stlc.base
open import stlc.prop
open import stlc.subst

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Relation.Nullary using (¬_; contradiction)
open import Data.Empty using (⊥; ⊥-elim)

data ClosEnv : (n : ℕ) → Set

data Clos : Set where
  ⟨_∣_⟩ : ∀ {n} → (M : Term n) → ClosEnv n → Clos
  _·_   : Clos → Clos → Clos
  if    : Clos → Clos → Clos → Clos
  true  : Clos
  false : Clos

data VClos : Clos → Set where
  V-true  : VClos true
  V-false : VClos false
  V-abs   : ∀ {n γ} {M : Term (suc n)} → VClos ⟨ ƛ M ∣ γ ⟩

infixl 5 _,'_

data ClosEnv where
  ∅'   : ClosEnv 0
  _,'_ : ∀ {n} → ClosEnv n → {c : Clos} → VClos c → ClosEnv (suc n)

lookup : ∀ {n} → Fin n → ClosEnv n → Clos
lookup fz     (_,'_ γ {c = c} V) = c
lookup (fs x) (γ ,' V) = lookup x γ

infix  4 E⊢_⊣_ C⊢_⦂_

data C⊢_⦂_ : Clos → Type → Set

data E⊢_⊣_ : ∀ {n} → ClosEnv n → Context n → Set where
  E⊢-∅ : E⊢ ∅' ⊣ ∅
  E⊢-, : ∀ {n Γ c A} {γ : ClosEnv n}
    → E⊢ γ ⊣ Γ
    → C⊢ c ⦂ A
    → (V : VClos c)
      -------------------
    → E⊢ γ ,' V ⊣ Γ ,- A

data C⊢_⦂_ where
  C⊢clos : ∀ {n γ Γ A} {M : Term n}
    → E⊢ γ ⊣ Γ
    → Γ ⊢ M ⦂ A
      -----------------
    → C⊢ ⟨ M ∣ γ ⟩ ⦂ A

  C⊢app : ∀ {c c₁ A B}
    → C⊢ c ⦂ A ⇒ B
    → C⊢ c₁ ⦂ A
      --------------
    → C⊢ c · c₁ ⦂ B

  C⊢if : ∀ {c c₁ c₂ A}
    → C⊢ c ⦂ bool
    → C⊢ c₁ ⦂ A
    → C⊢ c₂ ⦂ A
      ------------------
    → C⊢ if c c₁ c₂ ⦂ A

  C⊢true : C⊢ true ⦂ bool

  C⊢false : C⊢ false ⦂ bool

infix  4 _—→c_

data _—→c_ : Clos → Clos → Set where
  β-abs : ∀ {n c γ} {M : Term (suc n)}
    → (V : VClos c)
      -----------------------------------
    → ⟨ ƛ M ∣ γ ⟩ · c —→c ⟨ M ∣ γ ,' V ⟩

  ξ-app₁ : ∀ {c c' c₁}
    → c —→c c'
      -------------------
    → c · c₁ —→c c' · c₁

  ξ-app₂ : ∀ {c c₁ c₁'}
    → VClos c
    → c₁ —→c c₁'
      -------------------
    → c · c₁ —→c c · c₁'

  ξ-if : ∀ {c c' c₁ c₂}
    → c —→c c'
      ---------------------------
    → if c c₁ c₂ —→c if c' c₁ c₂

  β-if₁ : ∀ {c₁ c₂}
      --------------------
    → if true c₁ c₂ —→c c₁

  β-if₂ : ∀ {c₁ c₂}
      ----------------------
    → if false c₁ c₂ —→c c₂

  ν-var : ∀ {n γ c} {x : Fin n}
    → c ≡ lookup x γ
      ------------------
    → ⟨ ` x ∣ γ ⟩ —→c c

  ν-app : ∀ {n γ} {M N : Term n}
      ----------------------------------------
    → ⟨ M · N ∣ γ ⟩ —→c ⟨ M ∣ γ ⟩ · ⟨ N ∣ γ ⟩

  ν-if : ∀ {n γ} {L M N : Term n}
      ------------------------------------------------------
    → ⟨ if L M N ∣ γ ⟩ —→c if ⟨ L ∣ γ ⟩ ⟨ M ∣ γ ⟩ ⟨ N ∣ γ ⟩

  ν-true : ∀ {n} {γ : ClosEnv n} → ⟨ true ∣ γ ⟩ —→c true

  ν-false : ∀ {n} {γ : ClosEnv n} → ⟨ false ∣ γ ⟩ —→c false

lookup-∋ : ∀ {n Γ} {γ : ClosEnv n}
         → E⊢ γ ⊣ Γ → ∀ {A c x} → c ≡ lookup x γ → Γ ∋ x ⦂ A → C⊢ c ⦂ A
lookup-∋ (E⊢-, ⊢γ ⊢C V) refl Z      = ⊢C
lookup-∋ (E⊢-, ⊢γ ⊢C V) refl (S ∋x) = lookup-∋ ⊢γ refl ∋x

clos-pres : ∀ {c c' A} → C⊢ c ⦂ A → c —→c c' → C⊢ c' ⦂ A
clos-pres (C⊢clos ⊢γ (⊢var x))              (ν-var z)       = lookup-∋ ⊢γ z x
clos-pres (C⊢clos ⊢γ (⊢app ⊢M ⊢N))          ν-app           = C⊢app (C⊢clos ⊢γ ⊢M) (C⊢clos ⊢γ ⊢N)
clos-pres (C⊢clos ⊢γ (⊢if ⊢L ⊢M ⊢N))        ν-if            = C⊢if (C⊢clos ⊢γ ⊢L) (C⊢clos ⊢γ ⊢M) (C⊢clos ⊢γ ⊢N)
clos-pres (C⊢clos ⊢γ ⊢true)                 ν-true          = C⊢true
clos-pres (C⊢clos ⊢γ ⊢false)                ν-false         = C⊢false
clos-pres (C⊢app (C⊢clos ⊢γ (⊢abs ⊢M)) ⊢C₁) (β-abs V)       = C⊢clos (E⊢-, ⊢γ ⊢C₁ V) ⊢M
clos-pres (C⊢app ⊢C ⊢C₁)                    (ξ-app₁ c→c')   = C⊢app (clos-pres ⊢C c→c') ⊢C₁
clos-pres (C⊢app ⊢C ⊢C₁)                    (ξ-app₂ x c→c') = C⊢app ⊢C (clos-pres ⊢C₁ c→c')
clos-pres (C⊢if ⊢C ⊢C₁ ⊢C₂)                 (ξ-if c→c')     = C⊢if (clos-pres ⊢C c→c') ⊢C₁ ⊢C₂
clos-pres (C⊢if ⊢C ⊢C₁ ⊢C₂)                 β-if₁           = ⊢C₁
clos-pres (C⊢if ⊢C ⊢C₁ ⊢C₂)                 β-if₂           = ⊢C₂

clos-prog : ∀ {c A} → C⊢ c ⦂ A → VClos c ⊎ ∃[ c' ] c —→c c'
clos-prog (C⊢clos ⊢γ (⊢var x))                = inj₂ (_ , ν-var refl)
clos-prog (C⊢clos ⊢γ (⊢abs ⊢M))               = inj₁ V-abs
clos-prog (C⊢clos ⊢γ (⊢app ⊢M ⊢N))            = inj₂ (_ , ν-app)
clos-prog (C⊢clos ⊢γ ⊢true)                   = inj₂ (true , ν-true)
clos-prog (C⊢clos ⊢γ ⊢false)                  = inj₂ (false , ν-false)
clos-prog (C⊢clos ⊢γ (⊢if ⊢M ⊢M₁ ⊢M₂))        = inj₂ (_ , ν-if)
clos-prog (C⊢app ⊢C ⊢C₁) with clos-prog ⊢C
... | inj₂ (c' , c→c' )                       = inj₂ (_ , ξ-app₁ c→c')
... | inj₁ V-abs with clos-prog ⊢C₁
... | inj₁ vc₁                                = inj₂ (_ , β-abs vc₁)
... | inj₂ (c₁' , c₁→c₁')                     = inj₂ (_ , ξ-app₂ V-abs c₁→c₁')
clos-prog (C⊢if ⊢C ⊢C₁ ⊢C₂) with clos-prog ⊢C
clos-prog (C⊢if (C⊢clos x ()) ⊢C₁ ⊢C₂) | inj₁ V-abs
... | inj₁ V-true                             = inj₂ (_ , β-if₁)
... | inj₁ V-false                            = inj₂ (_ , β-if₂)
... | inj₂ (c' , c→c')                        = inj₂ (_ , ξ-if c→c')
clos-prog C⊢true                              = inj₁ V-true
clos-prog C⊢false                             = inj₁ V-false
