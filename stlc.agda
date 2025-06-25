module stlc where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _≤?_)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Data.Fin using (Fin; fromℕ<) renaming (zero to fz; suc to fs)

infixr 7 _⇒_

data Type : Set where
  bool : Type
  _⇒_  : Type → Type → Type

infix  5 ƛ_
infixl 7 _·_
infix  9 `_

data Term (n : ℕ) : Set where
  `_    : Fin n → Term n
  ƛ_    : Term (suc n) → Term n
  _·_   : Term n → Term n → Term n
  true  : Term n
  false : Term n
  if    : Term n → Term n → Term n → Term n

infix  9 #_
#_ : ∀ {n} (m : ℕ) → {m<n : True (suc m ≤? n)} → Term n
#_ m {m<n} = ` fromℕ< (toWitness m<n)

infixl 4 _,-_

data Context : ℕ → Set where
  ∅    : Context 0
  _,-_ : ∀ {n} → Context n → Type → Context (suc n)

infix  3 _∋_⦂_

data _∋_⦂_ : ∀ {n} → Context n → Fin n → Type → Set where
  Z : ∀ {n A} {Γ : Context n}
      ------------------
    → (Γ ,- A) ∋ fz ⦂ A

  S : ∀ {n x A B} {Γ : Context n}
    → Γ ∋ x ⦂ A
      --------------------
    → (Γ ,- B) ∋ fs x ⦂ A

infix  3 _⊢_⦂_

data _⊢_⦂_ {n} : Context n → Term n → Type → Set where
  ⊢var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      ------------
    → Γ ⊢ ` x ⦂ A

  ⊢abs : ∀ {Γ A B M}
    → Γ ,- A ⊢ M ⦂ B
      ---------------------
    → Γ ⊢ ƛ M ⦂ A ⇒ B

  ⊢app : ∀ {Γ A B M N}
    → Γ ⊢ M ⦂ A ⇒ B
    → Γ ⊢ N ⦂ A
      --------------
    → Γ ⊢ M · N ⦂ B

  ⊢true : ∀ {Γ}
      ----------------
    → Γ ⊢ true ⦂ bool

  ⊢false : ∀ {Γ}
      -----------------
    → Γ ⊢ false ⦂ bool

  ⊢if : ∀ {Γ L M N A}
    → Γ ⊢ L ⦂ bool
    → Γ ⊢ M ⦂ A
    → Γ ⊢ N ⦂ A
      -----------------
    → Γ ⊢ if L M N ⦂ A

data Value {n} : Term n → Set where
  V-abs : ∀ {M}
      ------------
    → Value (ƛ M)

  V-true : Value true

  V-false : Value false

ext : ∀ {n m : ℕ} → (Fin n → Fin m) → Fin (suc n) → Fin (suc m)
ext ρ fz     = fz
ext ρ (fs x) = fs (ρ x)

rename : ∀ {n m} → (Fin n → Fin m) → Term n → Term m
rename ρ (` x)      = ` ρ x
rename ρ (ƛ M)      = ƛ rename (ext ρ) M
rename ρ (M · N)    = (rename ρ M) · (rename ρ N)
rename ρ true       = true
rename ρ false      = false
rename ρ (if L M N) = if (rename ρ L) (rename ρ M) (rename ρ N)

exts : ∀ {n m} → (Fin n → Term m) → Fin (suc n) → Term (suc m)
exts σ fz     = ` fz
exts σ (fs x) = rename fs (σ x)

subst : ∀ {n m} → (Fin n → Term m) → Term n → Term m
subst σ (` x)      = σ x
subst σ (ƛ M)      = ƛ subst (exts σ) M
subst σ (M · N)    = (subst σ M) · (subst σ N)
subst σ true       = true
subst σ false      = false
subst σ (if L M N) = if (subst σ L) (subst σ M) (subst σ N)

subst-zero : ∀ {n} → Term n → (Fin (suc n) → Term n)
subst-zero N fz     = N
subst-zero N (fs x) = ` x

_[_] : ∀ {n} → Term (suc n) → Term n → Term n
M [ N ] = subst (subst-zero N) M

infix  3 _—→_

data _—→_ {n} : Term n → Term n → Set where
  ξ-app₁ : ∀ {M M' N}
    → M —→ M'
      ----------------
    → M · N —→ M' · N

  ξ-app₂ : ∀ {M N N'}
    → Value M
    → N —→ N'
      ----------------
    → M · N —→ M · N'

  β-abs : ∀ {M N}
    → Value N
      ---------------------
    → (ƛ M) · N —→ M [ N ]

  ξ-if : ∀ {L L' M N}
    → L —→ L'
      ----------------------
    → if L M N —→ if L' M N

  β-if₁ : ∀ {M N}
      -----------------
    → if true M N —→ M

  β-if₂ : ∀ {M N}
      -------------------
    → if false M N —→ N

