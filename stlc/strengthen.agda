module stlc.strengthen where

open import stlc.base
open import stlc.subst using (extensionality)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; _≢_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Fin.Properties using (punchInᵢ≢i)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Relation.Nullary using (Dec; yes; no; ¬_; contradiction; contraposition)
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
ty-antirename (⊢abs ⊢M)        {N = ƛ N}        Φ refl
  = ⊢abs (ty-antirename ⊢M {N = N} (λ { {x = fz} Z → Z ; {x = fs x} (S ∋x) → S (Φ ∋x) }) refl)
ty-antirename (⊢app ⊢M ⊢M₁)    {N = N · N₁}     Φ refl
  = ⊢app (ty-antirename ⊢M {N = N} Φ refl) (ty-antirename ⊢M₁ {N = N₁} Φ refl)
ty-antirename ⊢true            {N = true}       Φ refl = ⊢true
ty-antirename ⊢false           {N = false}      Φ refl = ⊢false
ty-antirename (⊢if ⊢M ⊢M₁ ⊢M₂) {N = if N N₁ N₂} Φ refl
  = ⊢if (ty-antirename ⊢M {N = N} Φ refl) (ty-antirename ⊢M₁ {N = N₁} Φ refl) (ty-antirename ⊢M₂ {N = N₂} Φ refl)

ty-strengthen : ∀ {M A B} {Γ : Context n}
  → Γ ,- B ⊢ rename fs M ⦂ A
    -------------------------
  → Γ ⊢ M ⦂ A
ty-strengthen ⊢M = ty-antirename ⊢M (λ { {x = fz} (S ∋x) → ∋x ; {x = fs x} (S ∋x) → ∋x }) refl

infix  3 _∈_

-- variable x is used in term M
_∈_ : Fin n → Term n → Set
x ∈ (` y)    = x ≡ y
x ∈ (ƛ M)    = fs x ∈ M
x ∈ (M · N)  = x ∈ M ⊎ x ∈ N
x ∈ true     = ⊥
x ∈ false    = ⊥
x ∈ if L M N = x ∈ L ⊎ x ∈ M ⊎ x ∈ N

punchIn-ext : ∀ {k : Fin (suc n)} → Fin.punchIn (fs k) ≡ ext (Fin.punchIn k)
punchIn-ext = extensionality lemma
  where
    lemma : ∀ {k} (x : Fin (suc n)) → Fin.punchIn (fs k) x ≡ ext (Fin.punchIn k) x
    lemma {k = fz}   fz     = refl
    lemma {k = fs k} fz     = refl
    lemma {k = fz}   (fs x) = refl
    lemma {k = fs k} (fs x) = refl

punchIn-∃ : ∀ (k x : Fin (suc n)) → k ≢ x → ∃[ y ] x ≡ Fin.punchIn k y
punchIn-∃ fz          fz          ev = ⊥-elim (ev refl)
punchIn-∃ fz          (fs x)      ev = x , refl
punchIn-∃ (fs fz)     fz          ev = fz , refl
punchIn-∃ (fs (fs k)) fz          ev = fz , refl
punchIn-∃ (fs fz)     (fs fz)     ev = ⊥-elim (ev refl)
punchIn-∃ (fs (fs k)) (fs fz)     ev with y , w ← punchIn-∃ (fs k) fz (λ z → ev (Eq.cong fs z)) = fs y , Eq.cong fs w
punchIn-∃ (fs fz) (fs (fs x))     ev with y , w ← punchIn-∃ fz (fs x) (λ z → ev (Eq.cong fs z)) = fs y , Eq.cong fs w
punchIn-∃ (fs (fs k)) (fs (fs x)) ev with y , w ← punchIn-∃ (fs k) (fs x) (λ z → ev (Eq.cong fs z)) = fs y , Eq.cong fs w

k∉M-N↑ : ∀ {k} {M : Term (suc n)} → ¬ (k ∈ M) → ∃[ N ] M ≡ rename (Fin.punchIn k) N
k∉M-N↑ {k = k} {M = ` x} ev with y , w ← punchIn-∃ k x ev = ` y , Eq.cong `_ w
k∉M-N↑ {M = ƛ M} ev with N , refl ← k∉M-N↑ {M = M} ev = ƛ N , Eq.cong (λ x → ƛ rename x N) punchIn-ext
k∉M-N↑ {M = M · M₁} ev
  with N  , refl ← k∉M-N↑ {M = M} (λ z → ev (inj₁ z))
  |    N₁ , refl ← k∉M-N↑ {M = M₁} (λ z → ev (inj₂ z))
  = N · N₁ , refl
k∉M-N↑ {M = true}  ev = true , refl
k∉M-N↑ {M = false} ev = false , refl
k∉M-N↑ {M = if M M₁ M₂} ev
  with N  , refl ← k∉M-N↑ {M = M} (λ z → ev (inj₁ z))
  |    N₁ , refl ← k∉M-N↑ {M = M₁} (λ z → ev (inj₂ (inj₁ z)))
  |    N₂ , refl ← k∉M-N↑ {M = M₂} (λ z → ev (inj₂ (inj₂ z)))
  = if N N₁ N₂ , refl

N↑-k∉M : ∀ {k N} {M : Term (suc n)} → M ≡ rename (Fin.punchIn k) N → ¬ (k ∈ M)
N↑-k∉M {N = ` x} {M = ` y} refl z = punchInᵢ≢i _ _ (Eq.sym z)
N↑-k∉M {N = ƛ N} {M = ƛ M} refl = N↑-k∉M {N = N} {M = M} (Eq.cong (λ z → rename z N) (Eq.sym punchIn-ext))
N↑-k∉M {N = N · N₁} {M = M · M₁} refl (inj₁ x) = N↑-k∉M {N = N} {M = M} refl x
N↑-k∉M {N = N · N₁} {M = M · M₁} refl (inj₂ x) = N↑-k∉M {N = N₁} {M = M₁} refl x
N↑-k∉M {N = true} {M = true} refl = λ ()
N↑-k∉M {N = false} {M = false} refl = λ ()
N↑-k∉M {N = if N N₁ N₂} {M = if M M₁ M₂} refl (inj₁ x) = N↑-k∉M {N = N} {M = M} refl x
N↑-k∉M {N = if N N₁ N₂} {M = if M M₁ M₂} refl (inj₂ (inj₁ x)) = N↑-k∉M {N = N₁} {M = M₁} refl x
N↑-k∉M {N = if N N₁ N₂} {M = if M M₁ M₂} refl (inj₂ (inj₂ x)) = N↑-k∉M {N = N₂} {M = M₂} refl x
