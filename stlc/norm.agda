module stlc.norm where

open import stlc.base
open import stlc.prop
open —→*-Reasoning
open import stlc.subst

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Relation.Nullary using (¬_; contradiction)
open import Data.Empty using (⊥; ⊥-elim)

private
  variable
    n m : ℕ

data Halts (M : Term n) : Set where
  halts : ∀ {N}
    → M —→* N
    → Value N
      --------
    → Halts M

-- logical relation predicate for normalization
𝒩_⟦_⟧ : Type → Term 0 → Set
𝒩 bool  ⟦ M ⟧ = ∅ ⊢ M ⦂ bool  × Halts M
𝒩 A ⇒ B ⟦ M ⟧ = ∅ ⊢ M ⦂ A ⇒ B × Halts M × (∀ {N} → 𝒩 A ⟦ N ⟧ → 𝒩 B ⟦ M · N ⟧)

-- well typed substitution
_⊨_ : (Fin n → Term 0) → Context n → Set
σ ⊨ Γ = ∀ {x B} → Γ ∋ x ⦂ B → 𝒩 B ⟦ σ x ⟧

⊢subst : ∀ {Γ : Context n} {σ M A}
  → Γ ⊢ M ⦂ A → σ ⊨ Γ
    ------------------
  → ∅ ⊢ subst σ M ⦂ A
⊢subst (⊢var Γ∋x) σ⊨Γ with σ⊨Γ Γ∋x
⊢subst {A = bool}  (⊢var Γ∋x) σ⊨Γ | ⊢σx , _ = ⊢σx
⊢subst {A = A ⇒ B} (⊢var Γ∋x) σ⊨Γ | ⊢σx , _ = ⊢σx
⊢subst (⊢abs ⊢M) σ⊨Γ = ⊢abs (ty-subst ⊢M (lemma σ⊨Γ))
  where
    lemma : ∀ {Γ A B σ x} → σ ⊨ Γ → Γ ,- A ∋ x ⦂ B → ∅ ,- A ⊢ exts σ x ⦂ B
    lemma σ⊨Γ Z     = ⊢var Z
    lemma σ⊨Γ (S x) with σ⊨Γ x
    lemma {B = bool}  σ⊨Γ (S x) | ⊢σx , _ = ty-rename ⊢σx λ ()
    lemma {B = B ⇒ C} σ⊨Γ (S x) | ⊢σx , _ = ty-rename ⊢σx λ ()
⊢subst (⊢app ⊢M ⊢N)   σ⊨Γ = ⊢app (⊢subst ⊢M σ⊨Γ) (⊢subst ⊢N σ⊨Γ)
⊢subst ⊢true          σ⊨Γ = ⊢true
⊢subst ⊢false         σ⊨Γ = ⊢false
⊢subst (⊢if ⊢L ⊢M ⊢N) σ⊨Γ = ⊢if (⊢subst ⊢L σ⊨Γ) (⊢subst ⊢M σ⊨Γ) (⊢subst ⊢N σ⊨Γ)

⊢—→Halts : ∀ {M M' : Term 0} → M —→ M' → Halts M → Halts M'
⊢—→Halts M—→M' (halts (_ ∎) VN)                  = ⊥-elim (V-¬→ VN M—→M')
⊢—→Halts M—→M' (halts (_ —→⟨ M—→M'' ⟩ M—→*N) VN) rewrite —→-determ M—→M' M—→M'' = halts M—→*N VN

⊢—→Halts' : ∀ {M M' : Term 0} → M —→ M' → Halts M' → Halts M
⊢—→Halts' M—→M' (halts (_ ∎) VN)             = halts (step—→ _ (_ ∎) M—→M') VN
⊢—→Halts' M—→M' (halts (_ —→⟨ x ⟩ M—→*N) VN) = halts (_ —→⟨ M—→M' ⟩ _ —→⟨ x ⟩ M—→*N) VN

𝒩→⊢ : ∀ {M A} → 𝒩 A ⟦ M ⟧ → ∅ ⊢ M ⦂ A
𝒩→⊢ {A = bool}  (⊢M , _) = ⊢M
𝒩→⊢ {A = A ⇒ B} (⊢M , _) = ⊢M

⊢—→𝒩 : ∀ {M M' A} → M —→ M' → 𝒩 A ⟦ M ⟧ → 𝒩 A ⟦ M' ⟧
⊢—→𝒩 {A = bool}  M—→M' (⊢M , HM)     = preservation ⊢M M—→M' , ⊢—→Halts M—→M' HM
⊢—→𝒩 {A = A ⇒ B} M—→M' (⊢M , HM , k) = preservation ⊢M M—→M' , ⊢—→Halts M—→M' HM , λ z → ⊢—→𝒩 (ξ-app₁ M—→M') (k z)

⊢—→𝒩' : ∀ {M M' A} → ∅ ⊢ M ⦂ A → M —→ M' → 𝒩 A ⟦ M' ⟧ → 𝒩 A ⟦ M ⟧
⊢—→𝒩' {A = bool}  ⊢M M—→M' (⊢M' , HM')     = ⊢M , ⊢—→Halts' M—→M' HM'
⊢—→𝒩' {A = A ⇒ B} ⊢M M—→M' (⊢M' , HM' , k) = ⊢M , ⊢—→Halts' M—→M' HM' , λ z → ⊢—→𝒩' (⊢app ⊢M (𝒩→⊢ z)) (ξ-app₁ M—→M') (k z)

⊢—→*𝒩 : ∀ {M M' A} → M —→* M' → 𝒩 A ⟦ M ⟧ → 𝒩 A ⟦ M' ⟧
⊢—→*𝒩 (_ ∎)              nn = nn
⊢—→*𝒩 (_ —→⟨ x ⟩ M—→*M') nn = ⊢—→*𝒩 M—→*M' (⊢—→𝒩 x nn)

⊢—→*𝒩' : ∀ {M M' A} → ∅ ⊢ M ⦂ A → M —→* M' → 𝒩 A ⟦ M' ⟧ → 𝒩 A ⟦ M ⟧
⊢—→*𝒩' ⊢M (_ ∎)              nn = nn
⊢—→*𝒩' ⊢M (_ —→⟨ x ⟩ M—→*M') nn = ⊢—→𝒩' ⊢M x (⊢—→*𝒩' (preservation ⊢M x) M—→*M' nn)

-- adequacy
-- normalizing term halts
𝒩-halts : ∀ {M A} → 𝒩 A ⟦ M ⟧ → Halts M
𝒩-halts {A = bool}  (⊢M , HM)        = HM
𝒩-halts {A = A ⇒ B} (⊢M , nn' , HMN) = nn'

-- fundamental property
-- well typed term is normalizing
⊢𝒩 : ∀ {Γ : Context n} {σ : Fin n → Term 0} {M A}
  → Γ ⊢ M ⦂ A → σ ⊨ Γ
    ------------------
  → 𝒩 A ⟦ subst σ M ⟧

⊢𝒩 (⊢var x) σ⊨Γ = σ⊨Γ x
⊢𝒩 {σ = σ} {M = ƛ M} {A = A ⇒ B} (⊢abs ⊢M) σ⊨Γ = ⊢subst (⊢abs ⊢M) σ⊨Γ , halts (subst σ (ƛ M) ∎) V-abs , H
  where
    H : ∀ {N} → 𝒩 A ⟦ N ⟧ → 𝒩 B ⟦ (ƛ subst (exts σ) M) · N ⟧
    H {N} nn with halts {N = N'} N—→*N' VN' ← 𝒩-halts nn
        = ⊢—→*𝒩' (⊢app (⊢subst (⊢abs ⊢M) σ⊨Γ) (𝒩→⊢ nn)) lemma (⊢𝒩 ⊢M (λ { Z → ⊢—→*𝒩 N—→*N' nn ; (S x) → σ⊨Γ x }))
      where
        lemma : (ƛ subst (exts σ) M) · N —→* subst (N' • σ) M
        lemma rewrite sub-ext-sub {σ = σ} {M = M} {N = N'}
          = —→*-trans (appR-cong N—→*N')
              (step—→ ((ƛ subst (exts σ) M) · N') ((subst (exts σ) M [ N' ]) ∎) (β-abs VN'))
⊢𝒩 (⊢app ⊢M ⊢N) σ⊨Γ with ⊢σM , HσM , H ← ⊢𝒩 ⊢M σ⊨Γ = H (⊢𝒩 ⊢N σ⊨Γ)
⊢𝒩 {σ = σ} ⊢true  σ⊨Γ = ⊢true , halts (subst σ true ∎) V-true
⊢𝒩 {σ = σ} ⊢false σ⊨Γ = ⊢false , halts (subst σ false ∎) V-false
⊢𝒩 {σ = σ} {M = if L M N} {A = A} (⊢if ⊢L ⊢M ⊢N) σ⊨Γ with ⊢𝒩 ⊢L σ⊨Γ
... | ⊢σL , halts {N = L'} L—→*L' VL with Canonical-bool (—→*-pres ⊢σL L—→*L') VL
... | inj₁ refl = ⊢—→*𝒩' (⊢if ⊢σL (⊢subst ⊢M σ⊨Γ) (⊢subst ⊢N σ⊨Γ))
                         (—→*-trans (if-cong L—→*L')
                           (step—→ (if true (subst σ M) (subst σ N)) (subst σ M ∎) β-if₁)) (⊢𝒩 ⊢M σ⊨Γ)
... | inj₂ refl = ⊢—→*𝒩' (⊢if ⊢σL (⊢subst ⊢M σ⊨Γ) (⊢subst ⊢N σ⊨Γ))
                         (—→*-trans (if-cong L—→*L')
                           (step—→ (if false (subst σ M) (subst σ N)) (subst σ N ∎) β-if₂)) (⊢𝒩 ⊢N σ⊨Γ)

norm : ∀ {M A} → ∅ ⊢ M ⦂ A → Halts M
norm {M = M} ⊢M with 𝒩-halts (⊢𝒩 {σ = ids} ⊢M (λ ()))
... | HM rewrite sub-id {M = M} = HM
