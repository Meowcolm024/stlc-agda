module extra.mu where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl; _≡_; _≢_)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (id; _∘_)

-- stlc with recursive type
-- adapted from *System F in Agda, for Fun and Profit (2019)*
-- since we do not need to do the system f stuff and type normalization,
-- the formalization here is significantly simplier

data Kind : Set where
  ⋆ : Kind

infixl 5 _,⋆_

data Ctx⋆ : Set where
  ∅    :               Ctx⋆  -- empty context
  _,⋆_ : Ctx⋆ → Kind → Ctx⋆  -- context extension

infix  4 _∋⋆_

data _∋⋆_ : Ctx⋆ → Kind → Set where
  Z : ∀ {Φ J}            → Φ ,⋆ J ∋⋆ J
  S : ∀ {Φ J K} → Φ ∋⋆ J → Φ ,⋆ K ∋⋆ J

infix  2 _⊢⋆_

infix  9 `_
infixr 7 _⇒_
infixr 5 μ_

data _⊢⋆_ (Φ : Ctx⋆) : Kind → Set where
  `_  : ∀ {J} → Φ ∋⋆ J               → Φ ⊢⋆ J  -- type variable
  `ℕ  :                                Φ ⊢⋆ ⋆  -- base type
  _⇒_ :         Φ ⊢⋆ ⋆      → Φ ⊢⋆ ⋆ → Φ ⊢⋆ ⋆  -- function type
  μ_  :         Φ ,⋆ ⋆ ⊢⋆ ⋆          → Φ ⊢⋆ ⋆  -- recursive type
  
Ren⋆ : Ctx⋆ → Ctx⋆ → Set
Ren⋆ Φ Ψ = ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J

lift⋆ : ∀ {Φ Ψ} → Ren⋆ Φ Ψ → ∀ {K} → Ren⋆ (Φ ,⋆ K) (Ψ ,⋆ K)
lift⋆ ρ Z     = Z
lift⋆ ρ (S x) = S (ρ x)

ren⋆ : ∀ {Φ Ψ} → Ren⋆ Φ Ψ → ∀ {J} → Φ ⊢⋆ J → Ψ ⊢⋆ J
ren⋆ ρ (` x)   = ` (ρ x)
ren⋆ ρ `ℕ      = `ℕ
ren⋆ ρ (A ⇒ B) = (ren⋆ ρ A) ⇒ (ren⋆ ρ B)
ren⋆ ρ (μ A)   = μ (ren⋆ (lift⋆ ρ) A)

weaken⋆ : ∀ {Φ J K} → Φ ⊢⋆ J → Φ ,⋆ K ⊢⋆ J
weaken⋆ = ren⋆ S

Sub⋆ : Ctx⋆ → Ctx⋆ → Set
Sub⋆ Φ Ψ = ∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J

lifts⋆ : ∀ {Φ Ψ} → Sub⋆ Φ Ψ → ∀ {K} → Sub⋆ (Φ ,⋆ K) (Ψ ,⋆ K)
lifts⋆ σ Z     = ` Z
lifts⋆ σ (S x) = ren⋆ S (σ x)

sub⋆ : ∀ {Φ Ψ} → Sub⋆ Φ Ψ → ∀ {J} → Φ ⊢⋆ J → Ψ ⊢⋆ J
sub⋆ σ (` x)   = σ x
sub⋆ σ `ℕ      = `ℕ
sub⋆ σ (A ⇒ B) = sub⋆ σ A ⇒ sub⋆ σ B
sub⋆ σ (μ A)   = μ (sub⋆ (lifts⋆ σ) A)

extend⋆ : ∀ {Φ Ψ} → Sub⋆ Φ Ψ → ∀ {J} → Ψ ⊢⋆ J → Sub⋆ (Φ ,⋆ J) Ψ
extend⋆ σ A Z     = A
extend⋆ σ A (S x) = σ x

_[_]⋆ : ∀ {Φ J K} → Φ ,⋆ K ⊢⋆ J → Φ ⊢⋆ K → Φ ⊢⋆ J
B [ A ]⋆ = sub⋆ (extend⋆ `_ A) B

-- substitution lemmas for stlc, but at type level
postulate
  lift⋆-id : ∀ {Φ J K} (x : Φ ,⋆ K ∋⋆ J) → lift⋆ id x ≡ x
  
  lift⋆-comp : ∀ {Φ Ψ Θ} {ρ : Ren⋆ Φ Ψ} {ρ' : Ren⋆ Ψ Θ} {J K} (x : Φ ,⋆ K ∋⋆ J)
             → lift⋆ (ρ' ∘ ρ) x ≡ lift⋆ ρ' (lift⋆ ρ x)
             
  ren⋆-id : ∀ {Φ J} (A : Φ ⊢⋆ J) → ren⋆ id A ≡ A
  
  ren⋆-comp : ∀ {Φ Ψ Θ} {ρ : Ren⋆ Φ Ψ} {ρ' : Ren⋆ Ψ Θ} {J} (A : Φ ⊢⋆ J)
            → ren⋆ (ρ' ∘ ρ) A ≡ ren⋆ ρ' (ren⋆ ρ A)
            
  lifts⋆-id : ∀ {Φ J K} (x : Φ ,⋆ K ∋⋆ J) → lifts⋆ `_ x ≡ ` x
  
  lifts⋆-comp : ∀ {Φ Ψ Θ} {σ : Sub⋆ Φ Ψ } {σ' : Sub⋆ Ψ Θ} {J K} (x : Φ ,⋆ K ∋⋆ J)
              → lifts⋆ (sub⋆ σ' ∘ σ) x ≡ sub⋆ (lifts⋆ σ') (lifts⋆ σ x)
              
  sub⋆-id : ∀ {Φ J} (A : Φ ⊢⋆ J) → sub⋆ `_ A ≡ A
  
  sub⋆-var : ∀ {Φ Ψ} {σ : Sub⋆ Φ Ψ} {J} (x : Φ ∋⋆ J) → sub⋆ σ (` x) ≡ σ x

  sub⋆-comp : ∀ {Φ Ψ Θ} {σ : Sub⋆ Φ Ψ} {σ' : Sub⋆ Ψ Θ} {J} (A : Φ ⊢⋆ J)
            → sub⋆ (sub⋆ σ' ∘ σ) A ≡ sub⋆ σ' (sub⋆ σ A)

  ren[]⋆ : ∀{ϕ Θ J K} (ρ : Ren⋆ ϕ Θ)(A : ϕ ,⋆ K ⊢⋆ J) (B : ϕ ⊢⋆ K )
         → ren⋆ ρ (A [ B ]⋆) ≡ ren⋆ (lift⋆ ρ) A [ ren⋆ ρ B ]⋆

  weaken⋆-sub⋆ : ∀ {Φ Ψ} (σ : Sub⋆ Φ Ψ) {K} (A : Φ ⊢⋆ ⋆)
               → weaken⋆ (sub⋆ σ A) ≡ sub⋆ (lifts⋆ σ {K = K}) (weaken⋆ A)

  weaken⋆[] : ∀ {Φ K} (B : Φ ⊢⋆ K) → (A : Φ ⊢⋆ ⋆) → A ≡ weaken⋆ A [ B ]⋆

  sub⋆-[]⋆ : ∀ {ϕ Ψ K} (σ : Sub⋆ ϕ Ψ) (A : ϕ ⊢⋆ K) (B : ϕ ,⋆ K ⊢⋆ ⋆)
           → sub⋆ σ (B [ A ]⋆) ≡ (sub⋆ (lifts⋆ σ) B) [ sub⋆ σ A ]⋆

infixl 5 _,-_

data Ctx : Ctx⋆ → Set where
  ∅    :                          Ctx ∅         -- empty context
  _,⋆_ : ∀ {Φ} → Ctx Φ → ∀ J    → Ctx (Φ ,⋆ J)  -- extend type variable
  _,-_ : ∀ {Φ} → Ctx Φ → Φ ⊢⋆ ⋆ → Ctx Φ         -- extend term variable

infix  4 _∋_

data _∋_ : ∀ {Φ} → Ctx Φ → Φ ⊢⋆ ⋆ → Set where
  Z : ∀ {Φ Γ} {A : Φ ⊢⋆ ⋆}             → Γ ,- A ∋ A
  S : ∀ {Φ Γ} {A B : Φ ⊢⋆ ⋆}   → Γ ∋ A → Γ ,- B ∋ A          -- skip term variable
  T : ∀ {Φ Γ} {A : Φ ⊢⋆ ⋆} {K} → Γ ∋ A → Γ ,⋆ K ∋ weaken⋆ A  -- skip type variable

infix  2 _⊢_

infixr 5 ƛ_
infixl 7 _·_

data _⊢_ {Φ} (Γ : Ctx Φ) : Φ ⊢⋆ ⋆ → Set where
  `_     : ∀ {A}   → Γ ∋ A                  → Γ ⊢ A           -- variable
  ƛ_     : ∀ {A B} → Γ ,- A ⊢ B             → Γ ⊢ A ⇒ B       -- lambda
  _·_    : ∀ {A B} → Γ ⊢ A ⇒ B      → Γ ⊢ A → Γ ⊢ B           -- application
  fold   : ∀ A     → Γ ⊢ A [ μ A ]⋆         → Γ ⊢ μ A         -- fold
  unfold : ∀ {A}   → Γ ⊢ μ A                → Γ ⊢ A [ μ A ]⋆  -- unfold

conv∋ : ∀ {Φ Γ} {A B : Φ ⊢⋆ ⋆} → A ≡ B → Γ ∋ A → Γ ∋ B
conv∋ refl x = x

conv⊢ : ∀ {Φ Γ} {A B : Φ ⊢⋆ ⋆} → A ≡ B → Γ ⊢ A → Γ ⊢ B
conv⊢ refl M = M

Ren : ∀ {Φ Ψ} Γ Δ → Ren⋆ Φ Ψ → Set
Ren {Φ} Γ Δ ρ = ∀ {A : Φ ⊢⋆ ⋆} → Γ ∋ A → Δ ∋ ren⋆ ρ A

lift : ∀{Φ Ψ Γ Δ} {ρ⋆ : Ren⋆ Φ Ψ}
     → Ren Γ Δ ρ⋆
       ---------------------------------------------------
     → (∀ {B : Φ ⊢⋆ ⋆} → Ren (Γ ,- B) (Δ ,- ren⋆ ρ⋆ B) ρ⋆)
lift ρ Z     = Z
lift ρ (S x) = S (ρ x)

⋆lift : ∀{Φ Ψ Γ Δ} {ρ⋆ : Ren⋆ Φ Ψ}
      → Ren Γ Δ ρ⋆
        ------------------------------------------
      → (∀ {K} → Ren (Γ ,⋆ K) (Δ ,⋆ K) (lift⋆ ρ⋆))
⋆lift {Δ = Δ} ρ {K} (T {A = A} x) = conv∋ (Eq.trans (Eq.sym (ren⋆-comp A)) (ren⋆-comp A)) (T (ρ x))

ren : ∀ {Φ Ψ Γ Δ} {ρ⋆ : Ren⋆ Φ Ψ}
    → Ren Γ Δ ρ⋆
      ----------------------------------------
    → (∀ {A : Φ ⊢⋆ ⋆} → Γ ⊢ A → Δ ⊢ ren⋆ ρ⋆ A)
ren ρ (` x)              = ` (ρ x)
ren ρ (ƛ M)              = ƛ (ren (lift ρ) M)
ren ρ (M · N)            = (ren ρ M) · (ren ρ N)
ren ρ (fold A M)         = fold _ (conv⊢ (ren[]⋆ _ A (μ A)) (ren ρ M))
ren ρ (unfold {A = A} M) = conv⊢ (Eq.sym (ren[]⋆ _ A (μ A))) (unfold (ren ρ M))

weaken : ∀ {Φ Γ} {A B : Φ ⊢⋆ ⋆} → Γ ⊢ A → Γ ,- B ⊢ A
weaken {A = A} M = conv⊢ (ren⋆-id A) (ren (conv∋ (Eq.sym (ren⋆-id _)) ∘ S) M)

⋆weaken : ∀ {Φ Γ} {A : Φ ⊢⋆ ⋆} {K} → Γ ⊢ A → Γ ,⋆ K ⊢ weaken⋆ A
⋆weaken M = ren T M

Sub : ∀ {Φ Ψ} Γ Δ → Sub⋆ Φ Ψ → Set
Sub {Φ} Γ Δ ρ = ∀ {A : Φ ⊢⋆ ⋆} → Γ ∋ A → Δ ⊢ sub⋆ ρ A

lifts : ∀{Φ Ψ Γ Δ} (σ⋆ : Sub⋆ Φ Ψ)
      → Sub Γ Δ σ⋆
        -------------------------------------------------
      → ∀ {B : Φ ⊢⋆ ⋆} → Sub (Γ ,- B) (Δ ,- sub⋆ σ⋆ B) σ⋆
lifts _ σ Z     = ` Z
lifts _ σ (S x) = weaken (σ x)

⋆lifts : ∀{Φ Ψ Γ Δ}(σ⋆ : Sub⋆ Φ Ψ)
       → Sub Γ Δ σ⋆
         -----------------------------------------
       → ∀ {K} → Sub (Γ ,⋆ K) (Δ ,⋆ K) (lifts⋆ σ⋆)
⋆lifts σ⋆ σ (T {A = A} x) = conv⊢ (weaken⋆-sub⋆ σ⋆ A) (⋆weaken (σ x))

sub : ∀ {Φ Ψ Γ Δ} (σ⋆ : Sub⋆ Φ Ψ)
  → Sub Γ Δ σ⋆
    ----------------------------------------
  → (∀ {A : Φ ⊢⋆ ⋆} → Γ ⊢ A → Δ ⊢ sub⋆ σ⋆ A)
sub σ⋆ σ (` x)              = σ x
sub σ⋆ σ (ƛ M)              = ƛ (sub σ⋆ (lifts σ⋆ σ) M)
sub σ⋆ σ (M · N)            = (sub σ⋆ σ M) · (sub σ⋆ σ N)
sub σ⋆ σ (fold A M)         = fold _ (conv⊢ (sub⋆-[]⋆ σ⋆ (μ A) A) (sub σ⋆ σ M))
sub σ⋆ σ (unfold {A = A} M) = conv⊢ (Eq.sym (sub⋆-[]⋆ σ⋆ (μ A) A)) (unfold (sub σ⋆ σ M))

extend : ∀ {Φ Ψ Γ Δ}
  → (σ⋆ : ∀{K} → Φ ∋⋆ K → Ψ ⊢⋆ K)
  → (∀ {A : Φ ⊢⋆ ⋆} → Γ ∋ A → Δ ⊢ sub⋆ σ⋆ A)
  → ∀ {A : Φ ⊢⋆ ⋆} → (N : Δ ⊢ sub⋆ σ⋆ A)
    ---------------------------------------------
  → (∀ {B : Φ ⊢⋆ ⋆} → Γ ,- A ∋ B → Δ ⊢ sub⋆ σ⋆ B)
extend σ⋆ σ N Z     = N
extend σ⋆ σ N (S x) = σ x

_[_] : ∀ {Φ Γ} {A B : Φ ⊢⋆ ⋆} → Γ ,- B ⊢ A → Γ ⊢ B → Γ ⊢ A
_[_] {A = A} {B} M N =
  conv⊢ (sub⋆-id A)
    (sub `_ (extend `_
      (conv⊢ (Eq.sym (sub⋆-id _)) ∘ `_)
      (conv⊢ (Eq.sym (sub⋆-id B)) N)) M)

_⋆[_] : ∀ {Φ Γ K} {B : Φ ,⋆ K ⊢⋆ ⋆} → Γ ,⋆ K ⊢ B → (A : Φ ⊢⋆ K) → Γ ⊢ B [ A ]⋆
M ⋆[ A ] = sub (extend⋆ `_ A) lem M
  where
    lem : ∀ {Φ Γ K} {B : Φ ,⋆ K ⊢⋆ ⋆} {A : Φ ⊢⋆ K}
        → (x : Γ ,⋆ K ∋ B) → Γ ⊢ sub⋆ (extend⋆ `_ A) B
    lem (T x) = conv⊢ (weaken⋆[] _ _) (` x)

data Value {Φ Γ} : {A : Φ ⊢⋆ ⋆} → Γ ⊢ A → Set where
  V-ƛ    : ∀ {A B} (M : Γ ,- A ⊢ B)             → Value (ƛ M)
  V-fold : ∀ {A} {M : Γ ⊢ A [ μ A ]⋆} → Value M → Value (fold A M)

-- call by name reduction

infix  2 _—→_

data _—→_ {Φ Γ} : {A : Φ ⊢⋆ ⋆} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
  ξ-· : ∀ {A B} {M M' : Γ ⊢ A ⇒ B} {N : Γ ⊢ A}
    → M —→ M'
      ---------------
    → M · N —→ M' · N

  β-ƛ : ∀{A B} {M : Γ ,- A ⊢ B} {N : Γ ⊢ A}
      --------------------
    → (ƛ M) · N —→ M [ N ]

  ξ-wrap : ∀ {A} {M M' : Γ ⊢ A [ μ A ]⋆}
    → M —→ M'
      ---------------------
    → fold A M —→ fold A M'

  ξ-unfold : ∀{A} {M M' : Γ ⊢ μ A}
    → M —→ M'
      ---------------------
    → unfold M —→ unfold M'
    
  β-fold : ∀ {A} {M : Γ ⊢ A [ μ A ]⋆}
      ----------------------
    → unfold (fold A M) —→ M

progress : ∀ {A : ∅ ⊢⋆ ⋆} (M : ∅ ⊢ A) → Value M ⊎ ∃[ M' ] (M —→ M')
progress (ƛ M)                      = inj₁ (V-ƛ M)
progress (M · N) with progress M
... | inj₁ (V-ƛ M')                 = inj₂ ((M' [ N ]) , β-ƛ)
... | inj₂ (M' , M—→M')             = inj₂ (M' · N , ξ-· M—→M')
progress (fold A M) with progress M
... | inj₁ V                        = inj₁ (V-fold V)
... | inj₂ (M' , M—→M')             = inj₂ (fold A M' , ξ-wrap M—→M')
progress (unfold M) with progress M
... | inj₁ (V-fold {M = M'} V)      = inj₂ (M' , β-fold)
... | inj₂ (M' , M—→M')             = inj₂ (unfold M' , ξ-unfold M—→M')

