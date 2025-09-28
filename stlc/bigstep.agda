module stlc.bigstep where

open import stlc.base
open import stlc.prop
open stlc.prop.—→*-Reasoning
open import stlc.subst

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Relation.Nullary using (¬_; contradiction)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Function.Base using (_∘_)

ClosEnv : (n : ℕ) → Set

data Clos : Set where
  true  : Clos
  false : Clos
  ⟨_∣_⟩ : ∀ {n} → (M : Term n) → ClosEnv n → Clos

ClosEnv n = (x : Fin n) → Clos

∅' : ClosEnv 0
∅' ()

_,'_ : ∀ {n} → ClosEnv n → Clos → ClosEnv (suc n)
(γ ,' c) fz     = c
(γ ,' c) (fs x) = γ x

infix  3 _⊢_⇓_

data _⊢_⇓_ : ∀ {n} → ClosEnv n → Term n → Clos → Set where
  ⇓-var : ∀ {n} {γ : ClosEnv n} {x V}
    → γ x ≡ V
      ------------
    → γ ⊢ ` x ⇓ V

  ⇓-lam : ∀ {n} {γ : ClosEnv n} {M}
      ----------------------
    → γ ⊢ ƛ M ⇓ ⟨ ƛ M ∣ γ ⟩

  ⇓-app : ∀ {n m} {γ : ClosEnv n} {δ : ClosEnv m} {L M N U V}
    → γ ⊢ L ⇓ ⟨ ƛ N ∣ δ ⟩
    → γ ⊢ M ⇓ U
    → (δ ,' U) ⊢ N ⇓ V
      --------------------
    → γ ⊢ L · M ⇓ V

  ⇓-true : ∀ {n} {γ : ClosEnv n}
      ----------------
    → γ ⊢ true ⇓ true

  ⇓-false : ∀ {n} {γ : ClosEnv n}
      ------------------
    → γ ⊢ false ⇓ false

  ⇓-if₁ : ∀ {n} {γ : ClosEnv n} {L M N V}
    → γ ⊢ L ⇓ true
    → γ ⊢ M ⇓ V
      -----------------
    → γ ⊢ if L M N ⇓ V

  ⇓-if₂ : ∀ {n} {γ : ClosEnv n} {L M N V}
    → γ ⊢ L ⇓ false
    → γ ⊢ N ⇓ V
      -----------------
    → γ ⊢ if L M N ⇓ V

⇓-determ : ∀ {n} {γ : ClosEnv n} {M V V'}
  → γ ⊢ M ⇓ V → γ ⊢ M ⇓ V'
    -----------------------
  → V ≡ V'
⇓-determ (⇓-var refl) (⇓-var refl) = refl
⇓-determ ⇓-lam        ⇓-lam        = refl
⇓-determ (⇓-app M⇓V M⇓V₁ M⇓V₂) (⇓-app M⇓V' M⇓V₁' M⇓V₂')
  with refl ← ⇓-determ M⇓V M⇓V'
  |    refl ← ⇓-determ M⇓V₁ M⇓V₁'
  = ⇓-determ M⇓V₂ M⇓V₂'
⇓-determ ⇓-true ⇓-true = refl
⇓-determ ⇓-false ⇓-false = refl
⇓-determ (⇓-if₁ M⇓V M⇓V₁) (⇓-if₁ M⇓V' M⇓V₁') = ⇓-determ M⇓V₁ M⇓V₁'
⇓-determ (⇓-if₁ M⇓V M⇓V₁) (⇓-if₂ M⇓V' M⇓V₁') with () ← ⇓-determ M⇓V M⇓V'
⇓-determ (⇓-if₂ M⇓V M⇓V₁) (⇓-if₁ M⇓V' M⇓V'') with () ← ⇓-determ M⇓V M⇓V'
⇓-determ (⇓-if₂ M⇓V M⇓V₁) (⇓-if₂ M⇓V' M⇓V'') = ⇓-determ M⇓V₁ M⇓V''

_≈_ : Clos → Term 0 → Set
_≈ₑ_ : ∀ {n} → ClosEnv n → (Fin n → Term 0) → Set

true                ≈ true  = ⊤
false               ≈ false = ⊤
(⟨_∣_⟩ {n} (ƛ M) γ) ≈ N     = Σ[ σ ∈ (Fin n → Term 0) ] (γ ≈ₑ σ) × (N ≡ subst σ (ƛ M))
_                   ≈ _     = ⊥

γ ≈ₑ σ = ∀ x → (γ x) ≈ (σ x)

Clos≈Value : ∀ {V : Clos} {M : Term 0} → V ≈ M → Value M
Clos≈Value {true}         {true}  V≈M = V-true
Clos≈Value {false}        {false} V≈M = V-false
Clos≈Value {⟨ ƛ M' ∣ γ ⟩} {ƛ M}   V≈M = V-abs

≈ₑ-ext : ∀ {n} {γ : ClosEnv n} {σ : Fin n → Term 0} {N V}
  → γ ≈ₑ σ → V ≈ N
    ----------------------------
  → (γ ,' V) ≈ₑ (ext-subst σ N)
≈ₑ-ext γ≈ₑσ V≈N fz     = V≈N
≈ₑ-ext {σ = σ} {N} γ≈ₑσ V≈N (fs x) rewrite subst-zero-exts {σ = σ} {M = N} {x = x} = γ≈ₑσ x


⇓→—→*×≈ : ∀ {n} {γ : ClosEnv n} {σ : Fin n → Term 0} {M V}
  → γ ⊢ M ⇓ V → γ ≈ₑ σ
    ------------------------------------------
  → Σ[ N ∈ Term 0 ] (subst σ M —→* N) × V ≈ N

⇓→—→*×≈ {σ = σ} (⇓-var {x = x} refl) γ≈ₑσ = subst σ (` x) , (subst σ (` x) ∎) , γ≈ₑσ x
⇓→—→*×≈ {σ = σ} {V = ⟨ ƛ M ∣ γ ⟩} ⇓-lam γ≈ₑσ = subst σ (ƛ M) , (subst σ (ƛ M) ∎) , σ , γ≈ₑσ , refl
⇓→—→*×≈ {σ = σ} (⇓-app {L = L} {M = M} {N = N} L⇓c M⇓U N⇓V) γ≈ₑσ
    with ⇓→—→*×≈ L⇓c γ≈ₑσ | ⇓→—→*×≈ M⇓U γ≈ₑσ
... | ƛ L' , L—→*L' , σ' , k , refl | M' , M—→*M' , U≈M'
    with ⇓→—→*×≈ {σ = ext-subst σ' M'} N⇓V (λ x → ≈ₑ-ext {σ = σ'} k U≈M' x)
... | N' , N—→*N' , V≈N' = N' , σLM→*N' , V≈N'
    where
      σLM→*N' : subst σ L · subst σ M —→* N'
      σLM→*N' rewrite Eq.sym (sub-sub {M = N} {σ₁ = exts σ'} {σ₂ = subst-zero M'})
        = —→*-trans (appL-cong L—→*L')
         (—→*-trans (appR-cong M—→*M')
                    (step—→ ((ƛ subst (exts σ') N) · M') N—→*N' (β-abs (Clos≈Value U≈M'))))
⇓→—→*×≈ {σ = σ} ⇓-true γ≈ₑσ = true , (subst σ true ∎) , tt
⇓→—→*×≈ {σ = σ} ⇓-false γ≈ₑσ = false , (subst σ false ∎) , tt
⇓→—→*×≈ (⇓-if₁ M⇓t M⇓V) γ≈ₑσ with ⇓→—→*×≈ M⇓t γ≈ₑσ | ⇓→—→*×≈ M⇓V γ≈ₑσ
... | true , L—→*true , tt | M' , M—→*M' , V≈M'
    = M' , —→*-trans (if-cong L—→*true) (step—→ (if true _ _) M—→*M' β-if₁) , V≈M'
⇓→—→*×≈ (⇓-if₂ M⇓f M⇓V) γ≈ₑσ  with ⇓→—→*×≈ M⇓f γ≈ₑσ | ⇓→—→*×≈ M⇓V γ≈ₑσ
... | false , L—→*false , tt | N' , M—→*N' , V≈N'
    = N' , —→*-trans (if-cong L—→*false) (step—→ (if false _ _) M—→*N' β-if₂) , V≈N'
