module stlc.clos where

open import stlc.base

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Relation.Nullary using (¬_; contradiction)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)

private
  variable
    n m : ℕ

ClosEnv : (n : ℕ) → Set

-- (proper) closure
data Clos : Set where
  ⟨_∣_⟩ : (M : Term n) → ClosEnv n → Clos
  _·_   : Clos → Clos → Clos
  if    : Clos → Clos → Clos → Clos
  true  : Clos
  false : Clos

data VClos : Clos → Set where
  V-true  : VClos true
  V-false : VClos false
  V-abs   : ∀ {γ} {M : Term (suc n)} → VClos ⟨ ƛ M ∣ γ ⟩

-- closure environment contains only values
ClosEnv n = (x : Fin n) → Σ[ c ∈ Clos ] VClos c

∅' : ClosEnv 0
∅' ()

_,'_ : ClosEnv n → {c : Clos} → VClos c → ClosEnv (suc n)
(γ ,' V) fz     = _ , V
(γ ,' V) (fs x) = γ x

infix  4 E⊢_⊣_ C⊢_⦂_

data C⊢_⦂_ : Clos → Type → Set

-- closure environment typing
E⊢_⊣_ : ClosEnv n → Context n → Set
E⊢ γ ⊣ Γ = ∀ {A x} → Γ ∋ x ⦂ A → C⊢ proj₁ (γ x) ⦂ A

-- closure typing
data C⊢_⦂_ where
  C⊢clos : ∀ {γ Γ A} {M : Term n}
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

infix  2 _—→c_

-- call by value reduction
data _—→c_ : Clos → Clos → Set where
  β-abs : ∀ {c γ} {M : Term (suc n)}
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

  ν-var : ∀ {γ} {x : Fin n}
      ----------------------------
    → ⟨ ` x ∣ γ ⟩ —→c proj₁ (γ x)

  ν-app : ∀ {γ} {M N : Term n}
      ----------------------------------------
    → ⟨ M · N ∣ γ ⟩ —→c ⟨ M ∣ γ ⟩ · ⟨ N ∣ γ ⟩

  ν-if : ∀ {γ} {L M N : Term n}
      ------------------------------------------------------
    → ⟨ if L M N ∣ γ ⟩ —→c if ⟨ L ∣ γ ⟩ ⟨ M ∣ γ ⟩ ⟨ N ∣ γ ⟩

  ν-true : ∀ {γ : ClosEnv n} → ⟨ true ∣ γ ⟩ —→c true

  ν-false : ∀ {γ : ClosEnv n} → ⟨ false ∣ γ ⟩ —→c false

clos-pres : ∀ {c c' A} → C⊢ c ⦂ A → c —→c c' → C⊢ c' ⦂ A
clos-pres (C⊢clos ⊢γ (⊢var x))              ν-var           = ⊢γ x
clos-pres (C⊢clos ⊢γ (⊢app ⊢M ⊢N))          ν-app           = C⊢app (C⊢clos ⊢γ ⊢M) (C⊢clos ⊢γ ⊢N)
clos-pres (C⊢clos ⊢γ (⊢if ⊢L ⊢M ⊢N))        ν-if            = C⊢if (C⊢clos ⊢γ ⊢L) (C⊢clos ⊢γ ⊢M) (C⊢clos ⊢γ ⊢N)
clos-pres (C⊢clos ⊢γ ⊢true)                 ν-true          = C⊢true
clos-pres (C⊢clos ⊢γ ⊢false)                ν-false         = C⊢false
clos-pres (C⊢app (C⊢clos ⊢γ (⊢abs ⊢M)) ⊢C₁) (β-abs V)       = C⊢clos (λ { Z → ⊢C₁ ; (S x) → ⊢γ x }) ⊢M
clos-pres (C⊢app ⊢C ⊢C₁)                    (ξ-app₁ c→c')   = C⊢app (clos-pres ⊢C c→c') ⊢C₁
clos-pres (C⊢app ⊢C ⊢C₁)                    (ξ-app₂ x c→c') = C⊢app ⊢C (clos-pres ⊢C₁ c→c')
clos-pres (C⊢if ⊢C ⊢C₁ ⊢C₂)                 (ξ-if c→c')     = C⊢if (clos-pres ⊢C c→c') ⊢C₁ ⊢C₂
clos-pres (C⊢if ⊢C ⊢C₁ ⊢C₂)                 β-if₁           = ⊢C₁
clos-pres (C⊢if ⊢C ⊢C₁ ⊢C₂)                 β-if₂           = ⊢C₂

clos-prog : ∀ {c A} → C⊢ c ⦂ A → VClos c ⊎ ∃[ c' ] (c —→c c')
clos-prog (C⊢clos ⊢γ (⊢var x))                = inj₂ (_ , ν-var)
clos-prog (C⊢clos ⊢γ (⊢abs ⊢M))               = inj₁ V-abs
clos-prog (C⊢clos ⊢γ (⊢app ⊢M ⊢N))            = inj₂ (_ , ν-app)
clos-prog (C⊢clos ⊢γ ⊢true)                   = inj₂ (true , ν-true)
clos-prog (C⊢clos ⊢γ ⊢false)                  = inj₂ (false , ν-false)
clos-prog (C⊢clos ⊢γ (⊢if ⊢M ⊢M₁ ⊢M₂))        = inj₂ (_ , ν-if)
clos-prog (C⊢app ⊢C ⊢C₁) with clos-prog ⊢C
... | inj₂ (c' , c→c' )                       = inj₂ (_ , ξ-app₁ c→c')
... | inj₁ V-abs with clos-prog ⊢C₁
...   | inj₁ vc₁                              = inj₂ (_ , β-abs vc₁)
...   | inj₂ (c₁' , c₁→c₁')                   = inj₂ (_ , ξ-app₂ V-abs c₁→c₁')
clos-prog (C⊢if ⊢C ⊢C₁ ⊢C₂) with clos-prog ⊢C
clos-prog (C⊢if (C⊢clos x ()) ⊢C₁ ⊢C₂) | inj₁ V-abs
... | inj₁ V-true                             = inj₂ (_ , β-if₁)
... | inj₁ V-false                            = inj₂ (_ , β-if₂)
... | inj₂ (c' , c→c')                        = inj₂ (_ , ξ-if c→c')
clos-prog C⊢true                              = inj₁ V-true
clos-prog C⊢false                             = inj₁ V-false

_≈_ : Clos → Term 0 → Set
_≈ₑ_ : ClosEnv n → (Fin n → Term 0) → Set

(⟨_∣_⟩ {n} M' γ) ≈ M        = Σ[ σ ∈ (Fin n → Term 0) ] (γ ≈ₑ σ) × (M ≡ subst σ M')
(c · c₁)         ≈ (M · N)  = (c ≈ M) × (c₁ ≈ N)
if c c₁ c₂       ≈ if L M N = (c ≈ L) × (c₁ ≈ M) × (c₂ ≈ N)
true             ≈ true     = ⊤
false            ≈ false    = ⊤
_                ≈ _        = ⊥

γ ≈ₑ σ = ∀ x → proj₁ (γ x) ≈ σ x

VClos≈Value : ∀ {c M} → VClos c → c ≈ M → Value M
VClos≈Value {M = true}  V-true  c≈M = V-true
VClos≈Value {M = false} V-false c≈M = V-false
VClos≈Value {M = ƛ M}   V-abs   c≈M = V-abs
