module extra.clos where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)

infixr 7 _⇒_

data Type : Set where
  bool : Type
  _⇒_  : Type → Type → Type

infixl 5 _,-_

data Context : Set where
  ∅    : Context
  _,-_ : Context → Type → Context

infix 4 _∋_

data _∋_ : Context → Type → Set where
  Z : ∀ {Γ A} → Γ ,- A ∋ A
  S : ∀ {Γ A B} → Γ ∋ A → Γ ,- B ∋ A

infix  4 _⊢_
infix  5 ƛ_
infixl 7 _·_
infix  9 `_

data _⊢_ : Context → Type → Set where
  `_  : ∀ {Γ A} → Γ ∋ A → Γ ⊢ A
  ƛ_  : ∀ {Γ A B} → Γ ,- A ⊢ B → Γ ⊢ A ⇒ B
  _·_ : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B

data ClosEnv : Context → Set

infixl 8 _[_]

data Clos : Type → Set where
  _[_] : ∀ {Γ A} → (M : Γ ⊢ A) → ClosEnv Γ → Clos A
  _·_  : ∀ {A B} → Clos (A ⇒ B) → Clos A → Clos B

data Value : ∀ {A} → Clos A → Set where
  V-ƛ : ∀ {Γ A B γ} {M : Γ ,- A ⊢ B} → Value ((ƛ M) [ γ ])

infixl 5 _,'_

data ClosEnv where
  ∅'   : ClosEnv ∅
  _,'_ : ∀ {γ A} → ClosEnv γ → {c : Clos A} → Value c → ClosEnv (γ ,- A)

lookup : ∀ {Γ A} → Γ ∋ A → ClosEnv Γ → Clos A
lookup Z     (_,'_ γ {c = c} V) = c
lookup (S x) (γ ,' V)           = lookup x γ

infix  4 _—→_

data _—→_ {A} : Clos A → Clos A → Set where
  β : ∀ {Γ B γ c} {M : Γ ,- B ⊢ A}
    → (V : Value c)
      --------------------------------
    → (ƛ M) [ γ ] · c —→ M [ γ ,' V ]

  ν : ∀ {B c₁} {c c' : Clos (B ⇒ A)}
    → c —→ c'
      ------------------
    → c · c₁ —→ c' · c₁

  μ : ∀ {B c₁ c₁'} {c : Clos (B ⇒ A)}
    → Value c
    → c₁ —→ c₁'
      ------------------
    → c · c₁ —→ c · c₁'

  var : ∀ {Γ c x} {γ : ClosEnv Γ}
    → c ≡ lookup x γ
      -----------------
    → (` x) [ γ ] —→ c

  app : ∀ {Γ γ B N} {M : Γ ⊢ B ⇒ A}
      -----------------------------------
    → (M · N) [ γ ] —→ M [ γ ] · N [ γ ]

progress : ∀ {A} → (c : Clos A) → Value c ⊎ ∃[ c' ] c —→ c'
progress (` x [ γ ])                               = inj₂ (lookup x γ , var refl)
progress ((ƛ M) [ γ ])                             = inj₁ V-ƛ
progress ((M · N) [ γ ])                           = inj₂ (M [ γ ] · N [ γ ] , app)
progress (c · c₁) with progress c
... | inj₂ (c' , c→c')                             = inj₂ (c' · c₁ , ν c→c')
... | inj₁ (V-ƛ {γ = γ} {M = M}) with progress c₁
... | inj₁ vc₁                                     = inj₂ (M [ γ ,' vc₁ ] , β vc₁)
... | inj₂ (c₁' , c₁→c₁')                          = inj₂ ((ƛ M) [ γ ] · c₁' , μ V-ƛ c₁→c₁')
