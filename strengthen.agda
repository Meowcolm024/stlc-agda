module strengthen where

open import stlc

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; _≢_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Relation.Nullary using (¬_; contradiction; contraposition)
open import Data.Empty using (⊥; ⊥-elim)

private
  variable
    n m : ℕ

¬⊎-¬× : ∀ {A B : Set} → ¬ (A ⊎ B) → (¬ A) × (¬ B)
¬⊎-¬× x = (λ z → x (inj₁ z)) , λ z → x (inj₂ z)

infix  3 _∈_

_∈_ : Fin n → Term n → Set
x ∈ (` y)    = x ≡ y
x ∈ (ƛ M)    = fs x ∈ M
x ∈ (M · N)  = x ∈ M ⊎ x ∈ N
x ∈ true     = ⊥
x ∈ false    = ⊥
x ∈ if L M N = x ∈ L ⊎ x ∈ M ⊎ x ∈ N

ext⁺ : ∀ (M : Term (suc n)) → (∀ (x : Fin n) → fs x ∈ M → Fin m) → ((x : Fin (suc n)) → x ∈ M → Fin (suc m))
ext⁺ M ρ fz     x∈M = fz
ext⁺ M ρ (fs x) x∈M = fs (ρ x x∈M)

-- conditional rename
rename⁺ : ∀ (M : Term n) → (∀ (x : Fin n) → x ∈ M → Fin m) → Term m
rename⁺ (` x)      ρ = ` ρ x refl
rename⁺ (ƛ M)      ρ = ƛ rename⁺ M (ext⁺ M ρ)
rename⁺ (M · N)    ρ = rename⁺ M (λ x z → ρ x (inj₁ z)) · rename⁺ N λ x z → ρ x (inj₂ z)
rename⁺ true       ρ = true
rename⁺ false      ρ = false
rename⁺ (if L M N) ρ = if (rename⁺ L λ x z → ρ x (inj₁ z)) (rename⁺ M λ x z → ρ x (inj₂ (inj₁ z))) (rename⁺ N λ x z → ρ x (inj₂ (inj₂ z)))

-- conditional stability under renaming
ty-rename⁺ : ∀ {M A} {Γ : Context n}
  → Γ ⊢ M ⦂ A
  → ∀ {m ρ} {Δ : Context m} → (∀ {x B} → (x∈M : x ∈ M) → Γ ∋ x ⦂ B → Δ ∋ ρ x x∈M ⦂ B)
    --------------------
  → Δ ⊢ rename⁺ M ρ ⦂ A
ty-rename⁺ (⊢var x)       Φ = ⊢var (Φ refl x)
ty-rename⁺ (⊢abs ⊢M)      Φ = ⊢abs (ty-rename⁺ ⊢M λ { x∈M Z → Z ; x∈M (S x) → S (Φ x∈M x) })
ty-rename⁺ (⊢app ⊢M ⊢N)   Φ = ⊢app (ty-rename⁺ ⊢M (λ x∈M → Φ (inj₁ x∈M))) (ty-rename⁺ ⊢N (λ x∈M → Φ (inj₂ x∈M)))
ty-rename⁺ ⊢true          Φ = ⊢true
ty-rename⁺ ⊢false         Φ = ⊢false
ty-rename⁺ (⊢if ⊢L ⊢M ⊢N) Φ = ⊢if (ty-rename⁺ ⊢L (λ x∈M → Φ (inj₁ x∈M)))
                                 (ty-rename⁺ ⊢M (λ x∈M → Φ (inj₂ (inj₁ x∈M))))
                                 (ty-rename⁺ ⊢N (λ x∈M → Φ (inj₂ (inj₂ x∈M))))

-- "downshift"
pred : ∀ (M : Term (suc n)) → ¬ (fz ∈ M) → ∀ (x : Fin (suc n)) → x ∈ M → Fin n
pred M z fz     x∈M = ⊥-elim (z x∈M)
pred M z (fs x) x∈M = x

strengthen⁺ : ∀ {M A B} {Γ : Context n}
  → Γ ,- B ⊢ M ⦂ A
  → (ev : ¬ (fz ∈ M))
    ------------------------------
  → Γ ⊢ rename⁺ M (pred M ev) ⦂ A
strengthen⁺ (⊢var Z)            ev = ⊥-elim (ev refl)
strengthen⁺ (⊢var (S x))        ev = ⊢var x
strengthen⁺ {M = ƛ M} (⊢abs ⊢M) ev = ⊢abs (ty-rename⁺ ⊢M λ { x∈M Z → Z ; x∈M (S Z) → S (⊥-elim (ev x∈M)) ; x∈M (S (S x)) → S x })
strengthen⁺ (⊢app ⊢M ⊢N) ev with p , q ← ¬⊎-¬× ev
  = ⊢app (ty-rename⁺ ⊢M λ { x∈M Z → ⊥-elim (p x∈M) ; x∈M (S x) → x })
        (ty-rename⁺ ⊢N λ { x∈M Z → ⊥-elim (q x∈M) ; x∈M (S x) → x })
strengthen⁺ ⊢true               ev = ⊢true
strengthen⁺ ⊢false              ev = ⊢false
strengthen⁺ (⊢if ⊢L ⊢M ⊢N)      ev with p , w ← ¬⊎-¬× ev with q , h ← ¬⊎-¬× w
  = ⊢if (ty-rename⁺ ⊢L λ { x∈M Z → ⊥-elim (p x∈M) ; x∈M (S x) → x })
       (ty-rename⁺ ⊢M λ { x∈M Z → ⊥-elim (q x∈M) ; x∈M (S x) → x })
       (ty-rename⁺ ⊢N λ { x∈M Z → ⊥-elim (h x∈M) ; x∈M (S x) → x })
