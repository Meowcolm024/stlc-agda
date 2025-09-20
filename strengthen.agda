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

ty-antirename : ∀ {M A} {Δ : Context m}
  → Δ ⊢ M ⦂ A
  → ∀ {N ρ} {Γ : Context n} → (∀ {x B} → Δ ∋ ρ x ⦂ B → Γ ∋ x ⦂ B)
  → M ≡ rename ρ N
    ---------------
  → Γ ⊢ N ⦂ A
ty-antirename (⊢var x)         {N = ` y}        Φ refl = ⊢var (Φ x)
ty-antirename (⊢abs ⊢M)        {N = ƛ N}        Φ refl = ⊢abs (ty-antirename ⊢M {N = N} (λ { {x = fz} Z → Z ; {x = fs x} (S ∋x) → S (Φ ∋x) }) refl)
ty-antirename (⊢app ⊢M ⊢M₁)    {N = N · N₁}     Φ refl = ⊢app (ty-antirename ⊢M {N = N} Φ refl) (ty-antirename ⊢M₁ {N = N₁} Φ refl)
ty-antirename ⊢true            {N = true}       Φ refl = ⊢true
ty-antirename ⊢false           {N = false}      Φ refl = ⊢false
ty-antirename (⊢if ⊢M ⊢M₁ ⊢M₂) {N = if N N₁ N₂} Φ refl = ⊢if (ty-antirename ⊢M {N = N} Φ refl) (ty-antirename ⊢M₁ {N = N₁} Φ refl) (ty-antirename ⊢M₂ {N = N₂} Φ refl)

ty-strengthen : ∀ {M A B} {Γ : Context n}
  → Γ ,- B ⊢ rename fs M ⦂ A
    -------------------------
  → Γ ⊢ M ⦂ A
ty-strengthen ⊢M = ty-antirename ⊢M (λ { {x = fz} (S ∋x) → ∋x ; {x = fs x} (S ∋x) → ∋x }) refl

-----
-- with conditional renaming
-----

infix  3 _∈_

_∈_ : Fin n → Term n → Set
x ∈ (` y)    = x ≡ y
x ∈ (ƛ M)    = fs x ∈ M
x ∈ (M · N)  = x ∈ M ⊎ x ∈ N
x ∈ true     = ⊥
x ∈ false    = ⊥
x ∈ if L M N = x ∈ L ⊎ x ∈ M ⊎ x ∈ N

ext⁺ : ∀ (M : Term (suc n)) → (∀ x → fs x ∈ M → Fin m) → (∀ x → x ∈ M → Fin (suc m))
ext⁺ M ρ fz     x∈M = fz
ext⁺ M ρ (fs x) x∈M = fs (ρ x x∈M)

-- conditional rename
rename⁺ : ∀ (M : Term n) → (∀ x → x ∈ M → Fin m) → Term m
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

-- "downshift", giving the condition 0 ∉ M
pred : ∀ (M : Term (suc n)) → ¬ (fz ∈ M) → (∀ x → x ∈ M → Fin n)
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
strengthen⁺ (⊢app ⊢M ⊢N) ev = ⊢app (ty-rename⁺ ⊢M λ { x∈M Z → ⊥-elim (ev (inj₁ x∈M)) ; x∈M (S x) → x })
                                  (ty-rename⁺ ⊢N λ { x∈M Z → ⊥-elim (ev (inj₂ x∈M)) ; x∈M (S x) → x })
strengthen⁺ ⊢true               ev = ⊢true
strengthen⁺ ⊢false              ev = ⊢false
strengthen⁺ (⊢if ⊢L ⊢M ⊢N)      ev = ⊢if (ty-rename⁺ ⊢L λ { x∈M Z → ⊥-elim (ev (inj₁ x∈M)) ; x∈M (S x) → x })
                                        (ty-rename⁺ ⊢M λ { x∈M Z → ⊥-elim (ev (inj₂ (inj₁ x∈M))) ; x∈M (S x) → x })
                                        (ty-rename⁺ ⊢N λ { x∈M Z → ⊥-elim (ev (inj₂ (inj₂ x∈M))) ; x∈M (S x) → x })

