module stlc.equiv where

open import stlc.base
open import stlc.subst

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Relation.Nullary using (¬_; contradiction; Dec; yes; no)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)

private
  variable
    n m : ℕ

open typing

infix  4 _⊢_≈_⦂_

data _⊢_≈_⦂_ {n} : Context n → Term n → Term n → Type → Set where
  ≈-refl : ∀ {Γ M A}
    → Γ ⊢ M ⦂ A
      --------------
    → Γ ⊢ M ≈ M ⦂ A

  ≈-sym : ∀ {Γ M N A}
    → Γ ⊢ N ≈ M ⦂ A
      --------------
    → Γ ⊢ M ≈ N ⦂ A

  ≈-trans : ∀ {Γ L M N A}
    → Γ ⊢ L ≈ M ⦂ A
    → Γ ⊢ M ≈ N ⦂ A
      ---------------
    → Γ ⊢ L ≈ N ⦂ A

  ≈-abs : ∀ {Γ M N A B}
    → Γ ,- A ⊢ M ≈ N ⦂ B
      ----------------------
    → Γ ⊢ ƛ M ≈ ƛ N ⦂ A ⇒ B

  ≈-app : ∀ {Γ M₁ M₂ N₁ N₂ A B}
    → Γ ⊢ M₁ ≈ M₂ ⦂ A ⇒ B
    → Γ ⊢ N₁ ≈ N₂ ⦂ A
      --------------------------
    → Γ ⊢ M₁ · N₁ ≈ M₂ · N₂ ⦂ B

  ≈-if : ∀ {Γ L₁ L₂ M₁ M₂ N₁ N₂ A}
    → Γ ⊢ L₁ ≈ L₂ ⦂ bool
    → Γ ⊢ M₁ ≈ M₂ ⦂ A
    → Γ ⊢ N₁ ≈ N₂ ⦂ A
      ----------------------------------
    → Γ ⊢ if L₁ M₁ N₁ ≈ if L₂ M₂ N₂ ⦂ A

  ≈-app-beta : ∀ {Γ M₁ M₂ N₁ N₂ A B}
    → Γ ,- A ⊢ M₁ ≈ M₂ ⦂ B
    → Γ ⊢ N₁ ≈ N₂ ⦂ A
      --------------------------------
    → Γ ⊢ (ƛ M₁) · N₁ ≈ M₂ [ N₂ ] ⦂ B

  -- extensionality
  -- the function argument is treated abstractly so it cannot be inspected
  -- e.g. even we know A is bool, we cannot do case analysis for true/false
  ≈-ext : ∀ {Γ M N A B}
    → Γ ,- A ⊢ (⟪ ↑ ⟫ M) · # 0 ≈ (⟪ ↑ ⟫ N) · # 0 ⦂ B
      ------------------
    → Γ ⊢ M ≈ N ⦂ A ⇒ B

  ≈-if-true : ∀ {Γ M₁ M₂ N₁ A}
    → Γ ⊢ M₁ ≈ M₂ ⦂ A
    → Γ ⊢ N₁ ⦂ A
      ---------------------------
    → Γ ⊢ if true M₁ N₁ ≈ M₂ ⦂ A

  ≈-if-false : ∀ {Γ M₁ N₁ N₂ A}
    → Γ ⊢ N₁ ≈ N₂ ⦂ A
    → Γ ⊢ M₁ ⦂ A
      --------------------------
    → Γ ⊢ if false M₁ N₁ ≈ N₂ ⦂ A

module example where
  _ : ∅ ⊢  ƛ # 0 ≈ ƛ if true (# 0) false ⦂ bool ⇒ bool
  _ = ≈-ext
      (≈-trans (≈-app-beta (≈-refl (⊢var Z)) (≈-refl (⊢var Z)))
      (≈-sym (≈-app-beta (≈-if-true (≈-refl (⊢var Z)) ⊢false) (≈-refl (⊢var Z)))))

