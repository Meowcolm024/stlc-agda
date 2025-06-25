module norm where

open import stlc
open import prop
open import subst

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_)
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

V-halts : ∀ {M : Term n} → Value M → Halts M
V-halts V-abs   = halts (_ ∎) V-abs
V-halts V-true  = halts (true ∎) V-true
V-halts V-false = halts (false ∎) V-false

𝐍_⟦_⟧ : Type → Term 0 → Set
𝐍 bool  ⟦ M ⟧ = ∅ ⊢ M ⦂ bool  × Halts M
𝐍 A ⇒ B ⟦ M ⟧ = ∅ ⊢ M ⦂ A ⇒ B × Halts M × (∀ {N} → 𝐍 A ⟦ N ⟧ → 𝐍 B ⟦ M · N ⟧)

𝐍→halts : ∀ {M A} → 𝐍 A ⟦ M ⟧ → Halts M
𝐍→halts {A = bool}  (⊢M , HM)        = HM
𝐍→halts {A = A ⇒ B} (⊢M , nn' , HMN) = nn'

_⊨_ : (Fin n → Term 0) → Context n → Set
σ ⊨ Γ = ∀ {x B} → Γ ∋ x ⦂ B → 𝐍 B ⟦ σ x ⟧

⊢subst : ∀ {Γ : Context n} {σ M A}
  → Γ ⊢ M ⦂ A → σ ⊨ Γ
    ------------------
  → ∅ ⊢ subst σ M ⦂ A
⊢subst (⊢var Γ∋x) σ⊨Γ with σ⊨Γ Γ∋x
⊢subst {A = bool}  (⊢var Γ∋x) σ⊨Γ | ⊢σx , _ = ⊢σx
⊢subst {A = A ⇒ B} (⊢var Γ∋x) σ⊨Γ | ⊢σx , _ = ⊢σx
⊢subst (⊢abs ⊢M) σ⊨Γ = ⊢abs (ty-subst ⊢M (ev σ⊨Γ))
  where
    ev : ∀ {Γ A B σ x} → σ ⊨ Γ → Γ ,- A ∋ x ⦂ B → ∅ ,- A ⊢ exts σ x ⦂ B
    ev σ⊨Γ Z     = ⊢var Z
    ev σ⊨Γ (S x) with σ⊨Γ x
    ev {B = bool}  σ⊨Γ (S x) | ⊢σx , _ = ty-rename ⊢σx λ ()
    ev {B = B ⇒ C} σ⊨Γ (S x) | ⊢σx , _ = ty-rename ⊢σx λ ()
⊢subst (⊢app ⊢M ⊢N)   σ⊨Γ = ⊢app (⊢subst ⊢M σ⊨Γ) (⊢subst ⊢N σ⊨Γ)
⊢subst ⊢true          σ⊨Γ = ⊢true
⊢subst ⊢false         σ⊨Γ = ⊢false
⊢subst (⊢if ⊢L ⊢M ⊢N) σ⊨Γ = ⊢if (⊢subst ⊢L σ⊨Γ) (⊢subst ⊢M σ⊨Γ) (⊢subst ⊢N σ⊨Γ)

⊢—→Halts : ∀ {M M' : Term 0} → M —→ M' → Halts M → Halts M'
⊢—→Halts M—→M' (halts (_ ∎) VN)                  = ⊥-elim (V-¬→ VN M—→M')
⊢—→Halts M—→M' (halts (_ —→⟨ M—→M'' ⟩ M—→*N) VN) rewrite —→determ M—→M' M—→M'' = halts M—→*N VN

⊢—→Halts' : ∀ {M M' : Term 0} → M —→ M' → Halts M' → Halts M
⊢—→Halts' M—→M' (halts (_ ∎) VN)             = halts (step—→ _ (_ ∎) M—→M') VN
⊢—→Halts' M—→M' (halts (_ —→⟨ x ⟩ M—→*N) VN) = halts (_ —→⟨ M—→M' ⟩ _ —→⟨ x ⟩ M—→*N) VN

𝐍→⊢ : ∀ {M A} → 𝐍 A ⟦ M ⟧ → ∅ ⊢ M ⦂ A
𝐍→⊢ {A = bool}  (⊢M , _) = ⊢M
𝐍→⊢ {A = A ⇒ B} (⊢M , _) = ⊢M

⊢—→𝐍 : ∀ {M M' A} → M —→ M' → 𝐍 A ⟦ M ⟧ → 𝐍 A ⟦ M' ⟧
⊢—→𝐍 {A = bool}  M—→M' (⊢M , HM)     = preservation ⊢M M—→M' , ⊢—→Halts M—→M' HM
⊢—→𝐍 {A = A ⇒ B} M—→M' (⊢M , HM , k) = preservation ⊢M M—→M' , ⊢—→Halts M—→M' HM , λ z → ⊢—→𝐍 (ξ-app₁ M—→M') (k z)

⊢—→𝐍' : ∀ {M M' A} → ∅ ⊢ M ⦂ A → M —→ M' → 𝐍 A ⟦ M' ⟧ → 𝐍 A ⟦ M ⟧
⊢—→𝐍' {A = bool}  ⊢M M—→M' (⊢M' , HM')     = ⊢M , ⊢—→Halts' M—→M' HM'
⊢—→𝐍' {A = A ⇒ B} ⊢M M—→M' (⊢M' , HM' , k) = ⊢M , ⊢—→Halts' M—→M' HM' , λ z → ⊢—→𝐍' (⊢app ⊢M (𝐍→⊢ z)) (ξ-app₁ M—→M') (k z)

⊢—→*𝐍 : ∀ {M M' A} → M —→* M' → 𝐍 A ⟦ M ⟧ → 𝐍 A ⟦ M' ⟧
⊢—→*𝐍 (_ ∎)              nn = nn
⊢—→*𝐍 (_ —→⟨ x ⟩ M—→*M') nn = ⊢—→*𝐍 M—→*M' (⊢—→𝐍 x nn)

⊢—→*𝐍' : ∀ {M M' A} → ∅ ⊢ M ⦂ A → M —→* M' → 𝐍 A ⟦ M' ⟧ → 𝐍 A ⟦ M ⟧
⊢—→*𝐍' ⊢M (_ ∎)              nn = nn
⊢—→*𝐍' ⊢M (_ —→⟨ x ⟩ M—→*M') nn = ⊢—→𝐍' ⊢M x (⊢—→*𝐍' (preservation ⊢M x) M—→*M' nn)

⊢𝐍 : ∀ {Γ : Context n} {σ : Fin n → Term 0} {M A}
  → Γ ⊢ M ⦂ A → σ ⊨ Γ
    ------------------
  → 𝐍 A ⟦ subst σ M ⟧
⊢𝐍 (⊢var x) σ⊨Γ = σ⊨Γ x
⊢𝐍 {σ = σ} {M = ƛ M} {A = A ⇒ B} (⊢abs ⊢M) σ⊨Γ = ⊢subst (⊢abs ⊢M) σ⊨Γ , halts (subst σ (ƛ M) ∎) V-abs , k
  where
    k : ∀ {N} → 𝐍 A ⟦ N ⟧ → 𝐍 B ⟦ (ƛ subst (exts σ) M) · N ⟧
    k {N} nn with 𝐍→halts nn
    ... | halts {N = N'} N—→*N' VN' = ⊢—→*𝐍' (⊢app (⊢subst (⊢abs ⊢M) σ⊨Γ) (𝐍→⊢ nn)) st (⊢𝐍 {σ = N' • σ} ⊢M (λ { Z → ⊢—→*𝐍 N—→*N' nn ; (S x) → σ⊨Γ x }))
      where
        st : (ƛ subst (exts σ) M) · N —→* subst (N' • σ) M
        st rewrite sub-ext-sub {σ = σ} {M = M} {N = N'}
          = —→*-trans (appR-cong V-abs N—→*N') (step—→ ((ƛ subst (exts σ) M) · N') ((subst (exts σ) M [ N' ]) ∎) (β-abs VN'))
⊢𝐍 (⊢app ⊢M ⊢N) σ⊨Γ with ⊢𝐍 ⊢M σ⊨Γ
... | ⊢σM , HσM , k = k (⊢𝐍 ⊢N σ⊨Γ)
⊢𝐍 {σ = σ} ⊢true  σ⊨Γ = ⊢true , halts (subst σ true ∎) V-true
⊢𝐍 {σ = σ} ⊢false σ⊨Γ = ⊢false , halts (subst σ false ∎) V-false
⊢𝐍 {σ = σ} {M = if L M N} {A = A} (⊢if ⊢L ⊢M ⊢N) σ⊨Γ with ⊢𝐍 ⊢L σ⊨Γ
... | ⊢σL , halts {N = L'} L—→*L' VL with Canonical-bool (—→*-pres ⊢σL L—→*L') VL
... | inj₁ refl = ⊢—→*𝐍' (⊢if ⊢σL (⊢subst ⊢M σ⊨Γ) (⊢subst ⊢N σ⊨Γ)) (—→*-trans (if-cong L—→*L') (step—→ (if true (subst σ M) (subst σ N)) (subst σ M ∎) β-if₁)) (⊢𝐍 ⊢M σ⊨Γ)
... | inj₂ refl = ⊢—→*𝐍' (⊢if ⊢σL (⊢subst ⊢M σ⊨Γ) (⊢subst ⊢N σ⊨Γ)) (—→*-trans (if-cong L—→*L') (step—→ (if false (subst σ M) (subst σ N)) (subst σ N ∎) β-if₂)) (⊢𝐍 ⊢N σ⊨Γ)

norm : ∀ {M A} → ∅ ⊢ M ⦂ A → Halts M
norm {M = M} ⊢M with 𝐍→halts (⊢𝐍 {σ = ids} ⊢M (λ ()))
... | HM rewrite sub-id {M = M} = HM
