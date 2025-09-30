module stlc.prop where

open import stlc.base

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

ty-rename : ∀ {M A} {Γ : Context n}
  → Γ ⊢ M ⦂ A
  → ∀ {m ρ} {Δ : Context m} → (∀ {x B} → Γ ∋ x ⦂ B → Δ ∋ ρ x ⦂ B)
    --------------------------------------------------------------
  → Δ ⊢ rename ρ M ⦂ A
ty-rename (⊢var x)       Φ = ⊢var (Φ x)
ty-rename (⊢abs ⊢M)      Φ = ⊢abs (ty-rename ⊢M λ { Z → Z ; (S ∋x) → S (Φ ∋x) })
ty-rename (⊢app ⊢M ⊢N)   Φ = ⊢app (ty-rename ⊢M Φ) (ty-rename ⊢N Φ)
ty-rename ⊢true          Φ = ⊢true
ty-rename ⊢false         Φ = ⊢false
ty-rename (⊢if ⊢L ⊢M ⊢N) Φ = ⊢if (ty-rename ⊢L Φ) (ty-rename ⊢M Φ) (ty-rename ⊢N Φ)

ty-subst : ∀ {M A} {Γ : Context n}
  → Γ ⊢ M ⦂ A
  → ∀ {m σ} {Δ : Context m} → (∀ {x B} → Γ ∋ x ⦂ B → Δ ⊢ σ x ⦂ B)
    --------------------------------------------------------------
  → Δ ⊢ subst σ M ⦂ A
ty-subst (⊢var x)       Φ = Φ x
ty-subst (⊢abs ⊢M)      Φ = ⊢abs (ty-subst ⊢M λ { Z → ⊢var Z ; (S ∋x) → ty-rename (Φ ∋x) S })
ty-subst (⊢app ⊢M ⊢N)   Φ = ⊢app (ty-subst ⊢M Φ) (ty-subst ⊢N Φ)
ty-subst ⊢true          Φ = ⊢true
ty-subst ⊢false         Φ = ⊢false
ty-subst (⊢if ⊢L ⊢M ⊢N) Φ = ⊢if (ty-subst ⊢L Φ) (ty-subst ⊢M Φ) (ty-subst ⊢N Φ)

----------------------
-- Basic Properties --
----------------------

preservation : ∀ {M M' A}
  → ∅ ⊢ M ⦂ A
  → M —→ M'
    -----------
  → ∅ ⊢ M' ⦂ A
preservation (⊢app ⊢M ⊢N)        (ξ-app₁ M→M') = ⊢app (preservation ⊢M M→M') ⊢N
preservation (⊢app ⊢M ⊢N)        (ξ-app₂ N→N') = ⊢app ⊢M (preservation ⊢N N→N')
preservation (⊢app (⊢abs ⊢M) ⊢N) (β-abs VN)    = ty-subst ⊢M λ { Z → ⊢N }
preservation (⊢if ⊢L ⊢M ⊢N)      (ξ-if L→L')   = ⊢if (preservation ⊢L L→L') ⊢M ⊢N
preservation (⊢if ⊢L ⊢M ⊢N)      β-if₁         = ⊢M
preservation (⊢if ⊢L ⊢M ⊢N)      β-if₂         = ⊢N

data Progress : Term n → Set where
  step : ∀ {M N : Term n}
    → M —→ N
      -----------
    → Progress M

  done : ∀ {M : Term n}
    → Value M
      -----------
    → Progress M

progress : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    -----------
  → Progress M
progress (⊢abs ⊢M)                       = done V-abs
progress (⊢app ⊢M ⊢N) with progress ⊢M
... | step M→M'                          = step (ξ-app₁ M→M')
... | done V-abs with progress ⊢N
...   | step N→N'                        = step (ξ-app₂ N→N')
...   | done VN                          = step (β-abs VN)
progress ⊢true                           = done V-true
progress ⊢false                          = done V-false
progress (⊢if ⊢L ⊢M ⊢N) with progress ⊢L
... | step L→L'                          = step (ξ-if L→L')
... | done V-true                        = step β-if₁
... | done V-false                       = step β-if₂

Canonical-bool : ∀ {M} {Γ : Context n}
  → Γ ⊢ M ⦂ bool
  → Value M
    ---------------------
  → M ≡ true ⊎ M ≡ false
Canonical-bool ⊢true  V-true  = inj₁ refl
Canonical-bool ⊢false V-false = inj₂ refl

Canonical-abs : ∀ {M A B} {Γ : Context n}
  → Γ ⊢ M ⦂ A ⇒ B
  → Value M
    ---------------
  → ∃[ N ] M ≡ ƛ N
Canonical-abs {M = ƛ N} (⊢abs ⊢N) V-abs = N , refl

V-¬→ : ∀ {M N : Term n}
  → Value M
    -----------
  → ¬ (M —→ N)
V-¬→ V-abs   ()
V-¬→ V-true  ()
V-¬→ V-false ()

—→-determ : ∀ {M N N' : Term n}
  → M —→ N → M —→ N'
    -----------------
  → N ≡ N'
—→-determ (ξ-app₁ M→N) (ξ-app₁ M→N') rewrite —→-determ M→N M→N' = refl
—→-determ (ξ-app₁ M→N) (ξ-app₂ M→N') = ⊥-elim (V-¬→ V-abs M→N)
—→-determ (ξ-app₂ M→N) (ξ-app₁ M→N') = ⊥-elim (V-¬→ V-abs M→N')
—→-determ (ξ-app₂ M→N) (ξ-app₂ M→N') rewrite —→-determ M→N M→N' = refl
—→-determ (ξ-app₂ M→N) (β-abs V')    = ⊥-elim (V-¬→ V' M→N)
—→-determ (β-abs V)    (ξ-app₂ M→N') = ⊥-elim (V-¬→ V M→N')
—→-determ (β-abs V)    (β-abs V')    = refl
—→-determ (ξ-if M→N)   (ξ-if M→N')   rewrite —→-determ M→N M→N' = refl
—→-determ β-if₁        β-if₁         = refl
—→-determ β-if₂        β-if₂         = refl

---------------
-- Multistep --
---------------

open multistep

—→*-trans : ∀ {L M N : Term n}
  → L —→* M → M —→* N
    ------------------
  → L —→* N
—→*-trans (_ ∎)             M—→*N = M—→*N
—→*-trans (_ —→⟨ x ⟩ L—→*M) M—→*N = step—→ _ (—→*-trans L—→*M M—→*N) x

—→*-pres : ∀ {A M M'} → ∅ ⊢ M ⦂ A → M —→* M' → ∅ ⊢ M' ⦂ A
—→*-pres ⊢M (_ ∎)              = ⊢M
—→*-pres ⊢M (_ —→⟨ x ⟩ M—→*M') = —→*-pres (preservation ⊢M x) M—→*M'

confluence : ∀ {L M M' : Term n}
  → L —→* M → L —→* M'
    ------------------------------
  → ∃[ N ] (M —→* N) × (M' —→* N)
confluence (L ∎)              (_ ∎)                = L , (L ∎) , (L ∎)
confluence (L ∎)              (_ —→⟨ L→M' ⟩ L→*M') = _ , step—→ L L→*M' L→M' , (_ ∎)
confluence (_ —→⟨ L→M ⟩ L→*M) (L ∎)                = _ , (_ ∎) , step—→ L L→*M L→M
confluence (_ —→⟨ L→M ⟩ L→*M) (_ —→⟨ L→M' ⟩ L→*M') rewrite —→-determ L→M L→M' = confluence L→*M L→*M'

if-cong : ∀ {L L' M N : Term n}
  → L —→* L'
    -----------------------
  → if L M N —→* if L' M N
if-cong (L ∎)                = if L _ _  ∎
if-cong (L —→⟨ L→L₁ ⟩ L→*L') = step—→ (if L _ _) (if-cong L→*L') (ξ-if L→L₁)

appL-cong : ∀ {M M' N : Term n}
  → M —→* M'
    -----------------
  → M · N —→* M' · N
appL-cong (M ∎)                = M · _ ∎
appL-cong (M —→⟨ M→M₁ ⟩ M→*M') = step—→ (M · _) (appL-cong M→*M') (ξ-app₁ M→M₁)

appR-cong : ∀ {M} {N N' : Term n}
  → N —→* N'
    -------------------------
  → (ƛ M) · N —→* (ƛ M) · N'
appR-cong (N ∎)                = _ · N ∎
appR-cong (N —→⟨ N→N₁ ⟩ N→*N') = step—→ (_ · N) (appR-cong N→*N') (ξ-app₂ N→N₁)

----------------
-- Evaluation --
----------------

module evaluation where
  record Gas : Set where
    constructor gas
    field
      amount : ℕ

  data Finished (N : Term 0) : Set where
    done :
      Value N
        -----------
      → Finished N

    out-of-gas :
        -----------
        Finished N

  data Steps : Term 0 → Set where
    steps : ∀ {L N}
      → L —→* N
      → Finished N
        ------------
      → Steps L

  eval : ∀ {M A}
    → Gas
    → ∅ ⊢ M ⦂ A
      -----------
    → Steps M
  eval {M} (gas zero)    ⊢M                   = steps (M ∎) out-of-gas
  eval {M} (gas (suc g)) ⊢M with progress ⊢M
  ... | done VM                               = steps (M ∎) (done VM)
  ... | step M→N with eval (gas g) (preservation ⊢M M→N)
  ...    | steps N→*L fin                     = steps (M —→⟨ M→N ⟩ N→*L) fin

