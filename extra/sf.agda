{-# OPTIONS --allow-unsolved-metas #-}
module extra.sf where

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
  _⟨_⟩ : Term n m → Type n → Term n m

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

_[_]⋆ : ∀ {n} → Type (suc n) → Type n → Type n
A [ B ]⋆ = subst⋆ (subst⋆-zero B) A

rename-ty : ∀ {n m r} → (Fin n → Fin r) → Term n m → Term r m
rename-ty ρ (lit x)   = lit x
rename-ty ρ (` x)     = ` x
rename-ty ρ (ƛ A ⇒ M) = ƛ rename⋆ ρ A ⇒ rename-ty ρ M
rename-ty ρ (M · N)   = rename-ty ρ M · rename-ty ρ N
rename-ty ρ (Λ M)     = Λ rename-ty (ext ρ) M
rename-ty ρ (M ⟨ A ⟩) = rename-ty ρ M ⟨ rename⋆ ρ A ⟩

rename : ∀ {n m s} → (Fin m → Fin s) → Term n m → Term n s
rename ρ (lit x)   = lit x
rename ρ (` x)     = ` ρ x
rename ρ (ƛ A ⇒ M) = ƛ A ⇒ rename (ext ρ) M
rename ρ (M · N)   = rename ρ M · rename ρ N
rename ρ (Λ M)     = Λ rename ρ M
rename ρ (M ⟨ A ⟩) = rename ρ M ⟨ A ⟩

exts : ∀ {n m s} → (Fin m → Term n s) → Fin (suc m) → Term n (suc s)
exts σ fz     = ` fz
exts σ (fs x) = rename fs (σ x)

ext-ty : ∀ {n m s} → (Fin m → Term n s) → Fin m → Term (suc n) s
ext-ty σ x = rename-ty fs (σ x)

subst : ∀ {n m s} → (Fin m → Term n s) → Term n m → Term n s
subst σ (lit x)   = lit x
subst σ (` x)     = σ x
subst σ (ƛ A ⇒ M) = ƛ A ⇒ subst (exts σ) M
subst σ (M · N)   = subst σ M · subst σ N
subst σ (Λ M)     = Λ subst (ext-ty σ) M
subst σ (M ⟨ A ⟩) = subst σ M ⟨ A ⟩

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
    → Γ ⊢ M ⦂ Π A
      -------------------------
    → Γ ⊢ M ⟨ B ⟩ ⦂ (A [ B ]⋆)

postulate
  rename⋆-fs-commute : ∀ {n m} {ρ : Fin n → Fin m} {A}
    → rename⋆ fs (rename⋆ ρ A) ≡ rename⋆ (ext ρ) (rename⋆ fs A)

  rename⋆-subst⋆-commute : ∀ {n m} {A : Type (suc n)} {B : Type n} {ρ : Fin n → Fin m}
    → (rename⋆ (ext ρ) A) [ rename⋆ ρ B ]⋆ ≡ rename⋆ ρ (A [ B ]⋆)

ty-rename-ty : ∀ {n m} {Γ : Context n m} {M A}
  → Γ ⊢ M ⦂ A
  → ∀ {r ρ} {Δ : Context r m}
      → (∀ {x} → Γ ∋ x ⦂⋆ → Δ ∋ ρ x ⦂⋆)
      → (∀ {x B} → Γ ∋ x ⦂ B → Δ ∋ x ⦂ rename⋆ ρ B)
    --------------------------------
  → Δ ⊢ rename-ty ρ M ⦂ rename⋆ ρ A
ty-rename-ty ⊢lit Φ Ψ = ⊢lit
ty-rename-ty (⊢var x) Φ Ψ = ⊢var (Ψ x)
ty-rename-ty (⊢abs ⊢M) Φ Ψ
  = ⊢abs (ty-rename-ty ⊢M (λ { (S- x) → S- (Φ x) })
         λ { Z → Z ; (S- x) → S- (Ψ x) })
ty-rename-ty (⊢app ⊢M ⊢N) Φ Ψ = ⊢app (ty-rename-ty ⊢M Φ Ψ) (ty-rename-ty ⊢N Φ Ψ)
ty-rename-ty (⊢tabs ⊢M) {Δ = Δ} Φ Ψ
  = ⊢tabs (ty-rename-ty ⊢M (λ { Z → Z ; (S⋆ x) → S⋆ (Φ x) })
          λ { (S⋆ x) → Eq.subst (λ z → Δ ,⋆ ∋ _ ⦂ z) rename⋆-fs-commute (S⋆ (Ψ x)) })
ty-rename-ty {M = M ⟨ B ⟩} (⊢tapp {A = A} ⊢M) {ρ = ρ} {Δ = Δ} Φ Ψ
  = Eq.subst (λ x → Δ ⊢ rename-ty ρ M ⟨ rename⋆ ρ B ⟩ ⦂ x)
    (rename⋆-subst⋆-commute {A = A} {B = B}) (⊢tapp (ty-rename-ty ⊢M Φ Ψ))

ty-rename : ∀ {n m} {Γ : Context n m} {M A}
  → Γ ⊢ M ⦂ A
  → ∀ {s ρ} {Δ : Context n s}
      → (∀ {x} → Γ ∋ x ⦂⋆ → Δ ∋ x ⦂⋆)
      → (∀ {x B} → Γ ∋ x ⦂ B → Δ ∋ ρ x ⦂ B)
    -------------------
  → Δ ⊢ rename ρ M ⦂ A
ty-rename ⊢lit         Φ Ψ = ⊢lit
ty-rename (⊢var x)     Φ Ψ = ⊢var (Ψ x)
ty-rename (⊢abs ⊢M)    Φ Ψ = ⊢abs (ty-rename ⊢M (λ { (S- x) → S- (Φ x)}) λ { Z → Z ; (S- x) → S- (Ψ x) })
ty-rename (⊢app ⊢M ⊢N) Φ Ψ = ⊢app (ty-rename ⊢M Φ Ψ) (ty-rename ⊢N Φ Ψ)
ty-rename (⊢tabs ⊢M)   Φ Ψ = ⊢tabs (ty-rename ⊢M (λ { Z → Z ; (S⋆ x) → S⋆ (Φ x) }) λ { (S⋆ x) → S⋆ (Ψ x) })
ty-rename (⊢tapp ⊢M)   Φ Ψ = ⊢tapp (ty-rename ⊢M Φ Ψ)

∋-unique : ∀ {n m} {Γ : Context n m} {x A A'}
         → Γ ∋ x ⦂ A → Γ ∋ x ⦂ A' → A ≡ A'
∋-unique Z      Z       = refl
∋-unique (S⋆ x) (S⋆ x') rewrite ∋-unique x x' = refl
∋-unique (S- x) (S- x') = ∋-unique x x'

⊢unique : ∀ {n m} {Γ : Context n m} {M A A'}
        → Γ ⊢ M ⦂ A → Γ ⊢ M ⦂ A' → A ≡ A'
⊢unique ⊢lit         ⊢lit           = refl
⊢unique (⊢var x)     (⊢var x')      = ∋-unique x x'
⊢unique (⊢abs ⊢M)    (⊢abs ⊢M')     rewrite ⊢unique ⊢M ⊢M' = refl
⊢unique (⊢app ⊢M ⊢N) (⊢app ⊢M' ⊢N') with refl ← ⊢unique ⊢N ⊢N' | refl ← ⊢unique ⊢M ⊢M' = refl
⊢unique (⊢tabs ⊢M)   (⊢tabs ⊢M')    with refl ← ⊢unique ⊢M ⊢M'  = refl
⊢unique (⊢tapp ⊢M)   (⊢tapp ⊢M')    with refl ← ⊢unique ⊢M ⊢M' = refl

postulate
  ext-inj : ∀ {n m} {ρ : Fin n → Fin m}
          → (∀ {x y} → ρ x ≡ ρ y → x ≡ y)
          → ∀ {x y} → ext ρ x ≡ ext ρ y → x ≡ y
  rename⋆-inj : ∀ {n m} {ρ : Fin n → Fin m}
              → (∀ {x y} → ρ x ≡ ρ y → x ≡ y)
              → ∀ {A B} → rename⋆ ρ A ≡ rename⋆ ρ B → A ≡ B

⇒-injL : ∀ {n} {A B A' B' : Type n} → A ⇒ B ≡ A' ⇒ B' → A ≡ A'
⇒-injL refl = refl

⇒-injR : ∀ {n} {A B A' B' : Type n} → A ⇒ B ≡ A' ⇒ B' → B ≡ B'
⇒-injR refl = refl

Γ,A∋0⦂A : ∀ {n m A B} {Γ : Context n m} → Γ ,- A ∋ fz ⦂ B → A ≡ B
Γ,A∋0⦂A Z = refl

-- does this postulate even holds?
rename⋆-∃ : ∀ {n m r M A ρ} {Γ : Context n m} {Δ : Context r m}
  → Δ ⊢ rename-ty ρ M ⦂ A
  → (∀ {x y} → ρ x ≡ ρ y → x ≡ y)
  → (∀ {x} → Δ ∋ ρ x ⦂⋆ → Γ ∋ x ⦂⋆)
  → (∀ {x C} → Δ ∋ x ⦂ rename⋆ ρ C → Γ ∋ x ⦂ C)
    -------------------------
  → ∃[ B ] (A ≡ rename⋆ ρ B)
rename⋆-∃ = {!!}

ty-antirename-ty : ∀ {r m} {Δ : Context r m} {N B}
  → Δ ⊢ N ⦂ B
  → ∀ {n M A ρ} {Γ : Context n m}
      → (∀ {x y} → ρ x ≡ ρ y → x ≡ y)
      → (∀ {x} → Δ ∋ ρ x ⦂⋆ → Γ ∋ x ⦂⋆)
      → (∀ {x C} → Δ ∋ x ⦂ rename⋆ ρ C → Γ ∋ x ⦂ C)
  → N ≡ rename-ty ρ M
  → B ≡ rename⋆ ρ A
    ----------------
  → Γ ⊢ M ⦂ A
ty-antirename-ty ⊢lit          {M = lit x}    {A = nat}    I Φ Ψ refl refl = ⊢lit
ty-antirename-ty (⊢var x)      {M = ` y}      {A = A}      I Φ Ψ refl refl = ⊢var (Ψ x)
ty-antirename-ty (⊢abs ⊢N)     {M = ƛ A' ⇒ M} {A = A ⇒ A₁} I Φ Ψ refl eb
  with refl ← rename⋆-inj I (⇒-injL eb) | refl ← ⇒-injR eb
  = ⊢abs (ty-antirename-ty ⊢N I
         (λ { {fz}   (S- ∋x) → S- (Φ ∋x) ; {fs x} (S- ∋x) → S- (Φ ∋x) })
         (λ { {fz}   ∋x      → Eq.subst (λ x → _ ,- A ∋ fz ⦂ x) (rename⋆-inj I (Γ,A∋0⦂A ∋x)) Z
            ; {fs x} (S- ∋x) → S- (Ψ ∋x) })
         refl refl)
ty-antirename-ty (⊢app ⊢N ⊢N₁) {M = M · M₁}   {A = A}      I Φ Ψ refl refl
  with A' , refl ← rename⋆-∃ ⊢N₁ I Φ Ψ
  = ⊢app (ty-antirename-ty ⊢N I Φ Ψ refl refl) (ty-antirename-ty ⊢N₁ I Φ Ψ refl refl)
ty-antirename-ty (⊢tabs ⊢N)    {M = Λ M}      {A = Π A}    I Φ Ψ refl refl
  = ⊢tabs (ty-antirename-ty ⊢N (ext-inj I)
    (λ { {fz} Z → Z ; {fs x} (S⋆ ∋x) → S⋆ (Φ ∋x) })
    (λ { {x} ∋x → {!!} }) -- we need to show C == rename fs C'
    refl refl)
ty-antirename-ty (⊢tapp ⊢N)    {M = M ⟨ A' ⟩} {A = A}      I Φ Ψ refl eb = {!!}
