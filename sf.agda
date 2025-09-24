module sf where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Relation.Nullary using (¬_; contradiction)
open import Data.Empty using (⊥; ⊥-elim)
open import Function.Base using (id; _∘_)

infix  9 `_
infixr 7 _⇒_
infix  5 Π_

data Type (n : ℕ) : Set where
  nat : Type n
  `_  : Fin n → Type n
  _⇒_ : Type n → Type n → Type n
  Π_  : Type (suc n) → Type n

infixl 7 _·_
infixl 7 _⟨_⟩
infix  5 ƛ_⇒_
infix  5 Λ_

data Term (n m : ℕ) : Set where
  lit  : ℕ → Term n m
  `_   : Fin m → Term n m
  ƛ_⇒_ : Type n → Term n (suc m) → Term n m
  _·_  : Term n m → Term n m → Term n m
  Λ_   : Term (suc n) m → Term n m
  _⟨_⟩ : Term (suc n) m → Type n → Term n m

ext : ∀ {n m} → (Fin n → Fin m) → Fin (suc n) → Fin (suc m)
ext ρ fz     = fz
ext ρ (fs x) = fs (ρ x)

rename⋆ : ∀ {n m} → (Fin n → Fin m) → Type n → Type m
rename⋆ ρ nat     = nat
rename⋆ ρ (` x)   = ` ρ x
rename⋆ ρ (A ⇒ B) = (rename⋆ ρ A) ⇒ (rename⋆ ρ B)
rename⋆ ρ (Π A)   = Π rename⋆ (ext ρ) A

↑⋆_ : ∀ {n} → Type n → Type (suc n)
↑⋆_ = rename⋆ fs

exts⋆ : ∀ {n m} → (Fin n → Type m) → Fin (suc n) → Type (suc m)
exts⋆ σ fz     = ` fz
exts⋆ σ (fs x) = rename⋆ fs (σ x)

subst⋆ : ∀ {n m} → (Fin n → Type m) → Type n → Type m
subst⋆ σ nat = nat
subst⋆ σ (` x) = σ x
subst⋆ σ (A ⇒ B) = (subst⋆ σ A) ⇒ (subst⋆ σ B)
subst⋆ σ (Π A) = Π subst⋆ (exts⋆ σ) A

subst⋆-zero : ∀ {n} → Type n → Fin (suc n) → Type n
subst⋆-zero A fz     = A
subst⋆-zero A (fs x) = ` x

_[_] : ∀ {n} → Type (suc n) → Type n → Type n
A [ B ] = subst⋆ (subst⋆-zero B) A

rename-ty : ∀ {n m r} → (Fin n → Fin r) → Term n m → Term r m
rename-ty ρ (lit x)   = lit x
rename-ty ρ (` x)     = ` x
rename-ty ρ (ƛ A ⇒ M) = ƛ rename⋆ ρ A ⇒ rename-ty ρ M
rename-ty ρ (M · N)   = (rename-ty ρ M) · (rename-ty ρ N)
rename-ty ρ (Λ M)     = Λ rename-ty (ext ρ) M
rename-ty ρ (M ⟨ A ⟩) = (rename-ty (ext ρ) M) ⟨ rename⋆ ρ A ⟩

-- not sure
rename : ∀ {n m s} → (Fin m → Fin s) → Term n m → Term n s
rename ρ (lit x)   = lit x
rename ρ (` x)     = ` ρ x
rename ρ (ƛ A ⇒ M) = ƛ A ⇒ rename (ext ρ) M
rename ρ (M · N)   = (rename ρ M) · (rename ρ N)
rename ρ (Λ M)     = Λ rename ρ M
rename ρ (M ⟨ A ⟩) = (rename ρ M) ⟨ A ⟩

exts : ∀ {n m s} → (Fin m → Term n s) → Fin (suc m) → Term n (suc s)
exts σ fz     = ` fz
exts σ (fs x) = rename fs (σ x)

ext-ty : ∀ {n m s} → (Fin m → Term n s) → Fin m → Term (suc n) s
ext-ty σ x = rename-ty fs (σ x)

subst : ∀ {n m s} → (Fin m → Term n s) → Term n m → Term n s
subst σ (lit x)   = lit x
subst σ (` x)     = σ x
subst σ (ƛ A ⇒ M) = ƛ A ⇒ subst (exts σ) M
subst σ (M · N)   = (subst σ M) · (subst σ N)
subst σ (Λ M)     = Λ subst (ext-ty σ) M
subst σ (M ⟨ A ⟩) = subst (ext-ty σ) M ⟨ A ⟩

infixl 5 _,⋆
infixl 4 _,-_

data Context : ℕ → ℕ → Set where
  ∅     : Context 0 0
  _,⋆  : ∀ {n m} → Context n m → Context (suc n) m
  _,-_ : ∀ {n m} → Context n m → Type n → Context n (suc m)

infix  3 _∋_⦂⋆
infix  3 _∋_⦂_

data _∋_⦂⋆ : ∀ {n m} → Context n m → Fin n → Set where
  Z : ∀ {n m} {Γ : Context n m}
      -------------
    → Γ ,⋆ ∋ fz ⦂⋆

  S⋆ : ∀ {n m x} {Γ : Context n m}
    → Γ ∋ x ⦂⋆
      ---------------
    → Γ ,⋆ ∋ fs x ⦂⋆

  S- : ∀ {n m x A} {Γ : Context n m}
    → Γ ∋ x ⦂⋆
      --------------
    → Γ ,- A ∋ x ⦂⋆

data _∋_⦂_ : ∀ {n m} → Context n m → Fin m → Type n → Set where
  Z : ∀ {n m A} {Γ : Context n m}
      ----------------
    → Γ ,- A ∋ fz ⦂ A

  S⋆ : ∀ {n m x A} {Γ : Context n m}
    → Γ ∋ x ⦂ A
      ------------------
    → Γ ,⋆ ∋ x ⦂ (↑⋆ A)

  S- : ∀ {n m x A B} {Γ : Context n m}
    → Γ ∋ x ⦂ A
      ------------------
    → Γ ,- B ∋ fs x ⦂ A

infix  3 _⊢_⦂_

data _⊢_⦂_ {n m} : Context n m → Term n m → Type n → Set where
  ⊢lit : ∀ {Γ x}
      ----------------
    → Γ ⊢ lit x ⦂ nat

  ⊢var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      ------------
    → Γ ⊢ ` x ⦂ A

  ⊢abs : ∀ {Γ M A B}
    → Γ ,- A ⊢ M ⦂ B
      --------------------
    → Γ ⊢ ƛ A ⇒ M ⦂ A ⇒ B

  ⊢app : ∀ {Γ M N A B}
    → Γ ⊢ M ⦂ A ⇒ B
    → Γ ⊢ N ⦂ A
      --------------
    → Γ ⊢ M · N ⦂ B

  ⊢tabs : ∀ {Γ M A}
    → Γ ,⋆ ⊢ M ⦂ A
      --------------
    → Γ ⊢ Λ M ⦂ Π A

  ⊢tapp : ∀ {Γ M A B}
    → Γ ⊢ Λ M ⦂ Π A
      ------------------------
    → Γ ⊢ M ⟨ B ⟩ ⦂ (A [ B ])

postulate
  rename⋆-fs-commute : ∀ {n m} {ρ : Fin n → Fin m} {A}
    → rename⋆ fs (rename⋆ ρ A) ≡ rename⋆ (ext ρ) (rename⋆ fs A)

  rename⋆-subst⋆-commute : ∀ {n m} {A : Type (suc n)} {B : Type n} {ρ : Fin n → Fin m}
    → (rename⋆ (ext ρ) A) [ rename⋆ ρ B ] ≡ rename⋆ ρ (A [ B ])

ty-rename-ty : ∀ {n m} {Γ : Context n m} {M A}
  → Γ ⊢ M ⦂ A
  → ∀ {r ρ} {Δ : Context r m}
      → (∀ {x} → Γ ∋ x ⦂⋆ → Δ ∋ ρ x ⦂⋆)
      → (∀ {x B} → Γ ∋ x ⦂ B → Δ ∋ x ⦂ rename⋆ ρ B)
    --------------------------------
  → Δ ⊢ rename-ty ρ M ⦂ rename⋆ ρ A
ty-rename-ty ⊢lit Φ Ψ = ⊢lit
ty-rename-ty (⊢var x) Φ Ψ = ⊢var (Ψ x)
ty-rename-ty (⊢abs ⊢M) Φ Ψ = ⊢abs (ty-rename-ty ⊢M (λ { (S- x) → S- (Φ x) }) λ { Z → Z ; (S- x) → S- (Ψ x) })
ty-rename-ty (⊢app ⊢M ⊢N) Φ Ψ = ⊢app (ty-rename-ty ⊢M Φ Ψ) (ty-rename-ty ⊢N Φ Ψ)
ty-rename-ty (⊢tabs ⊢M) {ρ = ρ} {Δ = Δ} Φ Ψ
  = ⊢tabs (ty-rename-ty ⊢M (λ { Z → Z ; (S⋆ x) → S⋆ (Φ x) }) λ { (S⋆ x) → Eq.subst (λ z → Δ ,⋆ ∋ _ ⦂ z) rename⋆-fs-commute (S⋆ (Ψ x)) })
ty-rename-ty (⊢tapp {A = A} {B = B} ⊢M) {ρ = ρ} Φ Ψ
  = Eq.subst (λ x → _ ⊢ rename-ty (ext ρ) _ ⟨ rename⋆ ρ _ ⟩ ⦂ x)
    (rename⋆-subst⋆-commute {A = A} {B = B} {ρ = ρ}) (⊢tapp (ty-rename-ty ⊢M Φ Ψ))

postulate
  ext-≡-inj : ∀ {n m} {ρ : Fin n → Fin m}
            → (∀ {x y} → ρ x ≡ ρ y → x ≡ y)
            → ∀ {x y} → ext ρ x ≡ ext ρ y → x ≡ y

  rename⋆-≡-inj : ∀ {n m} {ρ : Fin n → Fin m}
                → (∀ {x y} → ρ x ≡ ρ y → x ≡ y)
                → ∀ {A B} → rename⋆ ρ A ≡ rename⋆ ρ B → A ≡ B

⇒-≡-injL : ∀ {n} {A B A' B' : Type n} → A ⇒ B ≡ A' ⇒ B' → A ≡ A'
⇒-≡-injL refl = refl

⇒-≡-injR : ∀ {n} {A B A' B' : Type n} → A ⇒ B ≡ A' ⇒ B' → B ≡ B'
⇒-≡-injR refl = refl

∋-fz-uniq : ∀ {n m} {Γ : Context n m} {A B} → Γ ,- A ∋ fz ⦂ B → A ≡ B
∋-fz-uniq Z = refl

∋-uniq : ∀ {n m} {Γ : Context n m} {x A A'}
       → Γ ∋ x ⦂ A → Γ ∋ x ⦂ A' → A ≡ A'
∋-uniq Z Z = refl
∋-uniq (S⋆ x) (S⋆ x') rewrite ∋-uniq x x' = refl
∋-uniq (S- x) (S- x') = ∋-uniq x x'

⊢uniq : ∀ {n m} {Γ : Context n m} {M A A'}
      → Γ ⊢ M ⦂ A → Γ ⊢ M ⦂ A' → A ≡ A'
⊢uniq ⊢lit ⊢lit = refl
⊢uniq (⊢var x) (⊢var x₁) = ∋-uniq x x₁
⊢uniq (⊢abs ⊢M) (⊢abs ⊢M') rewrite ⊢uniq ⊢M ⊢M' = refl
⊢uniq (⊢app ⊢M ⊢N) (⊢app ⊢M' ⊢N') with refl ← ⊢uniq ⊢N ⊢N' | refl ← ⊢uniq ⊢M ⊢M' = refl
⊢uniq (⊢tabs ⊢M) (⊢tabs ⊢M') with refl ← ⊢uniq ⊢M ⊢M'  = refl
⊢uniq (⊢tapp ⊢M) (⊢tapp ⊢M') with refl ← ⊢uniq ⊢M ⊢M' = refl

ty-antirename-ty : ∀ {r m} {Δ : Context r m} {M A}
  → Δ ⊢ M ⦂ A
  → ∀ {n N B ρ} {Γ : Context n m}
    → (∀ {x y} → ρ x ≡ ρ y → x ≡ y)
    → (∀ {x} → Δ ∋ ρ x ⦂⋆ → Γ ∋ x ⦂⋆)
    → (∀ {x C} → Δ ∋ x ⦂ rename⋆ ρ C → Γ ∋ x ⦂ C)
  → M ≡ rename-ty ρ N
  → A ≡ rename⋆ ρ B
  → Γ ⊢ N ⦂ B
ty-antirename-ty ⊢lit {N = lit x} {B = nat} I Φ Ψ refl refl = ⊢lit
ty-antirename-ty (⊢var x) {N = ` x₁} {B = nat} I Φ Ψ refl refl = ⊢var (Ψ x)
ty-antirename-ty (⊢var x) {N = ` x₁} {B = ` x₂} I Φ Ψ refl refl = ⊢var (Ψ x)
ty-antirename-ty (⊢var x) {N = ` x₁} {B = B ⇒ B₁} I Φ Ψ refl refl = ⊢var (Ψ x)
ty-antirename-ty (⊢var x) {N = ` x₁} {B = Π B} I Φ Ψ refl refl = ⊢var (Ψ x)
ty-antirename-ty (⊢abs ⊢M) {N = ƛ T ⇒ N} {B = B₁ ⇒ B₂} {ρ = ρ} I Φ Ψ refl ev₂
  with refl ← rename⋆-≡-inj I (⇒-≡-injL ev₂)
  = ⊢abs (ty-antirename-ty ⊢M I
    (λ { (S- ∋x) → S- (Φ ∋x) })
    (λ { {x = fz} ∋x → Eq.subst (λ x → _ ,- x ∋ fz ⦂ _) (Eq.sym (rename⋆-≡-inj I (∋-fz-uniq ∋x))) Z ; {x = fs x} (S- ∋x) → S- (Ψ ∋x) })
    refl (⇒-≡-injR ev₂))
ty-antirename-ty (⊢app ⊢M ⊢M₁) {N = N · N₁} {B = B} {ρ = ρ} I Φ Ψ refl refl
  = ⊢app (ty-antirename-ty ⊢M I Φ Ψ refl (Eq.cong (_⇒ rename⋆ ρ B) {!!})) (ty-antirename-ty ⊢M₁ I Φ Ψ refl {!!})
ty-antirename-ty (⊢tabs ⊢M) {N = Λ N} {B = Π B} I Φ Ψ refl refl
  = ⊢tabs (ty-antirename-ty ⊢M
    (ext-≡-inj I)
    (λ { {x = fz} Z → Z ; {x = fs x} (S⋆ ∋x) → S⋆ (Φ ∋x) })
    (λ { ∋x → {!!} })
    refl refl)
ty-antirename-ty (⊢tapp (⊢tabs ⊢M)) {N = N ⟨ T ⟩} {B = B} I Φ Ψ refl ev₂ = {!!}
