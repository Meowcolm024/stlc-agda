module extra.unscoped where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary.Negation using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Function.Base using (_∘_)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

infix  4 _⊢_⦂_
infixr 7 _⇒_
infix  5 ƛ_
infixl 7 _·_
infix  9 `_
infix  6 _•_

data Type : Set where
  bool : Type
  _⇒_  : Type → Type → Type

-- functional context (infinite)
Context : Set
Context = ℕ → Type

-- cons A to subst (σ) or context (Γ)
_•_ : ∀ {A : Set} → A → (ℕ → A) → (ℕ → A)
(A • σ) 0       = A
(A • σ) (suc x) = σ x

data Term : Set where
  `_  : ℕ → Term
  ƛ_  : Term → Term
  _·_ : Term → Term → Term

data _⊢_⦂_ : Context → Term → Type → Set where
  ⊢var : ∀ {Γ x A}
    → Γ x ≡ A
      ------------
    → Γ ⊢ ` x ⦂ A

  ⊢abs : ∀ {Γ A B M}
    → A • Γ ⊢ M ⦂ B
      ----------------
    → Γ ⊢ ƛ M ⦂ A ⇒ B

  ⊢app : ∀ {Γ A B M N}
    → Γ ⊢ M ⦂ A ⇒ B
    → Γ ⊢ N ⦂ A
      --------------
    → Γ ⊢ M · N ⦂ B

ids : ℕ → Term
ids x = ` x

ext : (ℕ → ℕ) → (ℕ → ℕ)
ext ρ zero    = zero
ext ρ (suc x) = suc (ρ x)

rename : (ℕ → ℕ) → Term → Term
rename ρ (` x)   = ` ρ x
rename ρ (ƛ M)   = ƛ (rename (ext ρ) M)
rename ρ (M · N) = (rename ρ M) · (rename ρ N)

exts : (ℕ → Term) → (ℕ → Term)
exts σ zero    = ` zero
exts σ (suc x) = rename suc (σ x)

subst : (ℕ → Term) → Term → Term
subst σ (` x)   = σ x
subst σ (ƛ M)   = ƛ (subst (exts σ) M)
subst σ (M · N) = (subst σ M) · (subst σ N)

_[_] : Term → Term → Term
M [ N ] = subst (N • ids) M

ren : (ℕ → ℕ) → (ℕ → Term)
ren ρ = ids ∘ ρ

ren-ext : ∀ {ξ} → ren (ext ξ) ≡ exts (ren ξ)
ren-ext {ξ} = extensionality λ { zero → refl ; (suc x) → refl }

rename-subst-ren : ∀ {ρ M} → rename ρ M ≡ subst (ren ρ) M
rename-subst-ren {ρ} {` x}   = refl
rename-subst-ren {ρ} {ƛ M}   rewrite rename-subst-ren {ext ρ} {M} | ren-ext {ρ} = refl
rename-subst-ren {ρ} {M · N} rewrite rename-subst-ren {ρ} {M} | rename-subst-ren {ρ} {N} = refl

exts-subst-ren : ∀ {σ x} → exts σ (suc x) ≡ subst (ren suc) (σ x)
exts-subst-ren {σ} {x} rewrite rename-subst-ren {suc} {σ x} = refl

ty-ren : ∀ {Γ M A}
  → Γ ⊢ M ⦂ A
  → ∀ {Δ ρ} → (∀ x → Γ x ≡ Δ (ρ x))
    --------------------------------
  → Δ ⊢ subst (ren ρ) M ⦂ A
ty-ren (⊢var {x = x} refl) Φ = ⊢var (Eq.sym (Φ x))
ty-ren (⊢abs ⊢M) {ρ = ρ} Φ rewrite Eq.sym (ren-ext {ρ})
  = ⊢abs (ty-ren ⊢M (λ { zero → refl ; (suc x) → Φ x }))
ty-ren (⊢app ⊢M ⊢N) Φ = ⊢app (ty-ren ⊢M Φ) (ty-ren ⊢N Φ)

ty-subst : ∀ {Γ M A}
  → Γ ⊢ M ⦂ A
  → ∀ {σ Δ} → (∀ x → Δ ⊢ σ x ⦂ Γ x)
    --------------------------------
  → Δ ⊢ subst σ M ⦂ A
ty-subst (⊢var {x = x} refl) Φ = Φ x
ty-subst {Γ}(⊢abs {A = A} ⊢M) {σ} {Δ} Φ
  = ⊢abs (ty-subst ⊢M {exts σ} {A • Δ} lemma)
  where
    lemma : ∀ (x : ℕ) → A • Δ ⊢ exts σ x ⦂ (A • Γ) x
    lemma zero    = ⊢var refl
    lemma (suc x) rewrite exts-subst-ren {σ} {x} = ty-ren (Φ x) λ _ → refl
ty-subst (⊢app ⊢M ⊢N) Φ = ⊢app (ty-subst ⊢M Φ) (ty-subst ⊢N Φ)

data Value : Term → Set where
  V-abs : ∀ {M} → Value (ƛ M)

infix  4 _—→_

data _—→_ : Term → Term → Set where
  ξ-app₁ : ∀ {M M' N}
    → M —→ M'
      -----------------
    → M · N —→ M' · N

  ξ-app₂ : ∀ {M N N'}
    → N —→ N'
      ------------------------
    → (ƛ M) · N —→ (ƛ M) · N'

  β-abs : ∀ {M N}
    → Value N
      ---------------------
    → (ƛ M) · N —→ M [ N ]

ty-pres : ∀ {Γ M M' A}
  → Γ ⊢ M ⦂ A → M —→ M'
    --------------------
  → Γ ⊢ M' ⦂ A
ty-pres (⊢app ⊢M ⊢N)        (ξ-app₁ M→M') = ⊢app (ty-pres ⊢M M→M') ⊢N
ty-pres (⊢app ⊢M ⊢N)        (ξ-app₂ M→M') = ⊢app ⊢M (ty-pres ⊢N M→M')
ty-pres (⊢app (⊢abs ⊢M) ⊢N) (β-abs VN)    = ty-subst ⊢M λ { zero → ⊢N ; (suc x) → ⊢var refl }

-- closed context
Closed : Context → Set
Closed Γ = ∀ {x A} → ¬ (Γ x ≡ A)

ty-prog : ∀ {Γ M A}
  → Closed Γ → Γ ⊢ M ⦂ A
    --------------------------
  → Value M ⊎ ∃[ M' ] M —→ M'
ty-prog c (⊢var x)                               = ⊥-elim (c x)
ty-prog c (⊢abs ⊢M)                              = inj₁ V-abs
ty-prog c (⊢app {N = N} ⊢M ⊢N) with ty-prog c ⊢M
... | inj₂ (M' , M→M')                           = inj₂ (M' · N , ξ-app₁ M→M')
... | inj₁ (V-abs {M = M}) with ty-prog c ⊢N
...   | inj₁ (V-abs {M = N})                     = inj₂ ((M [ ƛ N ]) , β-abs V-abs)
...   | inj₂ (N' , N→N')                         = inj₂ ((ƛ M) · N' , ξ-app₂ N→N')
