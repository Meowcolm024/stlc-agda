module stlc.equiv where

open import stlc.base
open import stlc.prop
open import stlc.subst
import stlc.safety as safety
open safety using (—↛_; conf—↛join; appL—↛; appR—↛; if—↛)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Relation.Nullary using (¬_; contradiction; Dec; yes; no)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)

open typing
open multistep

private
  variable
    n m : ℕ

-- I'm not sure if the context part is correct
-- program context
data 𝒞 : ℕ → ℕ → Set where
  □               : ∀ {n} → 𝒞 n n
  ƛ[_]            : ∀ {n m} → 𝒞 (suc n) (suc m) → 𝒞 (suc n) m
  [_]·_           : ∀ {n m} → 𝒞 n m → Term m → 𝒞 n m
  _·[_]           : ∀ {n m} → Term m → 𝒞 n m → 𝒞 n m
  if[_]then_else_ : ∀ {n m} → 𝒞 n m → Term m → Term m → 𝒞 n m
  if_then[_]else_ : ∀ {n m} → Term m → 𝒞 n m → Term m → 𝒞 n m
  if_then_else[_] : ∀ {n m} → Term m → Term m → 𝒞 n m → 𝒞 n m

-- apply a context to a term
plug : 𝒞 n m → Term n → Term m
plug □                      M = M
plug ƛ[ C ]                 M = ƛ plug C M
plug ([ C ]· N)             M = plug C M · N
plug (M ·[ C ])             N = M · plug C N
plug (if[ C ]then M else N) L = if (plug C L) M N
plug (if L then[ C ]else N) M = if L (plug C M) N
plug if L then M else[ C ]  N = if L M (plug C N)

infix  4 _⦂_⊢_=⇒_⊢_
-- context typing
_⦂_⊢_=⇒_⊢_ : 𝒞 n m → Context n → Type → Context m → Type → Set
C ⦂ Γ ⊢ A =⇒ Δ ⊢ B = ∀ {M} → Γ ⊢ M ⦂ A → Δ ⊢ plug C M ⦂ B

_iff_ : Set → Set → Set
P iff Q = (P → Q) × (Q → P)

infix  4 _⊢_≈ctx_⦂_
-- contextual equivalence
_⊢_≈ctx_⦂_ : Context n → Term n → Term n → Type → Set
Γ ⊢ M ≈ctx N ⦂ A = ∀ C {B} → C ⦂ Γ ⊢ A =⇒ ∅ ⊢ B → ∀ V → Value V × (plug C M —→* V) iff (plug C N —→* V)

-- logical predicate for equivalence
ℰ⟦_⟧_is_ : Type → Term 0 → Term 0 → Set

𝒱⟦_⟧_is_ : Type → Term 0 → Term 0 → Set
𝒱⟦ bool  ⟧ true  is true  = ⊤
𝒱⟦ bool  ⟧ false is false = ⊤
𝒱⟦ A ⇒ B ⟧ (ƛ M) is (ƛ N) = ∀ M' N' → 𝒱⟦ A ⟧ M' is N' → ℰ⟦ B ⟧ (M [ M' ]) is (N [ N' ])
𝒱⟦ _     ⟧ _     is _     = ⊥

ℰ⟦ A ⟧ M is N = ∀ {M' N'} → (M —→* M') × (—↛ M') × (N —→* N') × (—↛ N') → 𝒱⟦ A ⟧ M' is N'

𝒢⟦_⟧ : Context n → (Fin n → Term 0) → (Fin n → Term 0) → Set
𝒢⟦ Γ ⟧ σ τ = ∀ {x A} → Γ ∋ x ⦂ A → 𝒱⟦ A ⟧ (σ x) is (τ x)

infix  4 _⊢_≈_⦂_
-- logical equivalence
_⊢_≈_⦂_ : Context n → Term n → Term n → Type → Set
Γ ⊢ M ≈ N ⦂ A = (Γ ⊢ M ⦂ A) × (Γ ⊢ N ⦂ A) × (∀ σ τ → 𝒢⟦ Γ ⟧ σ τ → ℰ⟦ A ⟧ (subst σ M) is (subst τ N))

𝒱—↛ : ∀ {M N A} → 𝒱⟦ A ⟧ M is N → (—↛ M) × (—↛ N)
𝒱—↛ {M = true}  {N = true}  {A = bool}  V = (λ { _ () }) , (λ { _ () })
𝒱—↛ {M = false} {N = false} {A = bool}  V = (λ { _ () }) , (λ { _ () })
𝒱—↛ {M = ƛ M}   {N = ƛ N}   {A = A ⇒ B} V = (λ { _ () }) , (λ { _ () })

𝒱-V : ∀ {M N A} → 𝒱⟦ A ⟧ M is N → Value M × Value N
𝒱-V {M = true}  {N = true}  {A = bool}  V = V-true , V-true
𝒱-V {M = false} {N = false} {A = bool}  V = V-false , V-false
𝒱-V {M = ƛ M}   {N = ƛ N}   {A = A ⇒ B} V = V-abs , V-abs

𝒱⟦⇒⟧-Canonical : ∀ {M N A B} → 𝒱⟦ A ⇒ B ⟧ M is N → (∃[ M' ] (M ≡ ƛ M')) × (∃[ N' ] (N ≡ ƛ N'))
𝒱⟦⇒⟧-Canonical {M = ƛ M} {N = ƛ N} V = (M , refl) , N , refl

𝒱⟦bool⟧-Canonical : ∀ {M N} → 𝒱⟦ bool ⟧ M is N → (M ≡ true × N ≡ true) ⊎ (M ≡ false × N ≡ false)
𝒱⟦bool⟧-Canonical {M = true}  {N = true}  V = inj₁ (refl , refl)
𝒱⟦bool⟧-Canonical {M = false} {N = false} V = inj₂ (refl , refl)

-- fundamental property
-- well typed term logically equals to itself
-- this is basically semantic typing...
⊢-≈ : ∀ {Γ : Context n} {A M}
  → Γ ⊢ M ⦂ A
    --------------
  → Γ ⊢ M ≈ M ⦂ A

⊢-≈ {Γ = Γ} {A = A} {M = ` x₁} (⊢var x) = ⊢var x , ⊢var x , lemma
  where
    lemma : ∀ σ τ → 𝒢⟦ Γ ⟧ σ τ → ℰ⟦ A ⟧ subst σ (` x₁) is subst τ (` x₁)
    lemma σ τ GG (M→*M' , VM' , N→*N' , VN')
      with —↛σx , —↛τx ← 𝒱—↛ (GG x)
      with refl ← safety.—↛-M→*M M→*M' —↛σx
      |    refl ← safety.—↛-M→*M N→*N' —↛τx
      = GG x
⊢-≈ {Γ = Γ} {A = A ⇒ B} {M = ƛ M} (⊢abs ⊢M) = ⊢abs ⊢M , ⊢abs ⊢M , lemma
  where
    lemma : ∀ σ τ → 𝒢⟦ Γ ⟧ σ τ → ℰ⟦ A ⇒ B ⟧ subst σ (ƛ M) is subst τ (ƛ M)
    lemma σ τ GG (M→*M' , VM' , N→*N' , VN')
      with refl ← safety.—↛-M→*M M→*M' (λ { _ () })
      |    refl ← safety.—↛-M→*M N→*N' (λ { _ () })
      = λ M' N' V' (st1 , v1 , st2 , v2) →
        let st1' : subst (M' • σ) M —→* _
            st1' = Eq.subst (λ x → x —→* _) (Eq.sym (sub-ext-sub {σ = σ} {M = M} {N = M'})) st1
            st2' : subst (N' • τ) M —→* _
            st2' = Eq.subst (λ x → x —→* _) (Eq.sym (sub-ext-sub {σ = τ} {M = M} {N = N'})) st2
        in proj₂ (proj₂ (⊢-≈ ⊢M)) (M' • σ) (N' • τ) (λ { Z → V' ; (S x) → GG x }) (st1' , v1 , st2' , v2)
⊢-≈ {Γ = Γ} {A = A} {M = M₁ · M₂} (⊢app ⊢M₁ ⊢M₂) = ⊢app ⊢M₁ ⊢M₂ , ⊢app ⊢M₁ ⊢M₂ , lemma
  where
    lemma : ∀ σ τ → 𝒢⟦ Γ ⟧ σ τ → ℰ⟦ A ⟧ subst σ (M₁ · M₂) is subst τ (M₁ · M₂)
    lemma σ τ GG (M→*M' , VM' , N→*N' , VN')
      with M₁' , σM₁→M₁' , —↛M₁' ← appL—↛ M→*M' VM'
      |    N₁' , τM₁→N₁' , —↛N₁' ← appL—↛ N→*N' VN'
      with VM₁ ← proj₂ (proj₂ (⊢-≈ ⊢M₁))  σ τ GG (σM₁→M₁' , —↛M₁' , τM₁→N₁' , —↛N₁')
      with (M₁'' , refl) , (N₁'' , refl) ← 𝒱⟦⇒⟧-Canonical VM₁
      with M₂' , σM₂→M₂' , —↛M₂' ← appR—↛ (conf—↛join M→*M' (—→*-trans (appL-cong σM₁→M₁') (_ ∎)) VM') VM'
      |    N₂' , τM₂→N₂' , —↛N₂' ← appR—↛ (conf—↛join N→*N' (—→*-trans (appL-cong τM₁→N₁') (_ ∎)) VN') VN'
      with VM₂ ← proj₂ (proj₂ (⊢-≈ ⊢M₂)) σ τ GG (σM₂→M₂' , —↛M₂' , τM₂→N₂' , —↛N₂')
      = VM₁ M₂' N₂' VM₂ (stM₁' , VM' , stM₂' , VN')
      where
        stM₁' = conf—↛join M→*M' (—→*-trans (appL-cong σM₁→M₁')
            (—→*-trans (appR-cong σM₂→M₂') (_ —→⟨ β-abs (proj₁ (𝒱-V VM₂)) ⟩ _ ∎))) VM'
        stM₂' = conf—↛join N→*N' (—→*-trans (appL-cong τM₁→N₁')
            (—→*-trans (appR-cong τM₂→N₂') (_ —→⟨ β-abs (proj₂ (𝒱-V VM₂)) ⟩ _ ∎))) VN'
⊢-≈ ⊢true = ⊢true , ⊢true , λ { σ τ GG  ((_ ∎) , VM' , (_ ∎) , VN') → tt }
⊢-≈ ⊢false = ⊢false , ⊢false , λ { σ τ GG  ((_ ∎) , VM' , (_ ∎) , VN') → tt }
⊢-≈ {Γ = Γ} {A = A} {M = if M₁ M₂ M₃} (⊢if ⊢M₁ ⊢M₂ ⊢M₃) = ⊢if ⊢M₁ ⊢M₂ ⊢M₃ , ⊢if ⊢M₁ ⊢M₂ ⊢M₃ , lemma
  where
    lemma : ∀ σ τ → 𝒢⟦ Γ ⟧ σ τ → ℰ⟦ A ⟧ subst σ (if M₁ M₂ M₃) is subst τ (if M₁ M₂ M₃)
    lemma σ τ GG (M→*M' , VM' , N→*N' , VN')
      with M₁' , σM₁→M₁' , –↛M₁' ← if—↛ M→*M' VM' | N₁' , τM₁→N₁' , —↛N₁' ← if—↛ N→*N' VN'
      with  _ , _ , K ← ⊢-≈ ⊢M₁
      with 𝒱⟦bool⟧-Canonical (K σ τ GG (σM₁→M₁' , –↛M₁' , τM₁→N₁' , —↛N₁'))
    ... | inj₁ (refl , refl) = proj₂ (proj₂ (⊢-≈ ⊢M₂)) σ τ GG (st1 , VM' , st2 , VN')
          where
            st1 = conf—↛join M→*M' (—→*-trans (if-cong σM₁→M₁') (_ —→⟨ β-if₁ ⟩ _ ∎)) VM'
            st2 = conf—↛join N→*N' (—→*-trans (if-cong τM₁→N₁') (_ —→⟨ β-if₁ ⟩ _ ∎)) VN'
    ... | inj₂ (refl , refl) = proj₂ (proj₂ (⊢-≈ ⊢M₃)) σ τ GG (st1 , VM' , st2 , VN')
          where
            st1 = conf—↛join M→*M' (—→*-trans (if-cong σM₁→M₁') (_ —→⟨ β-if₂ ⟩ _ ∎)) VM'
            st2 = conf—↛join N→*N' (—→*-trans (if-cong τM₁→N₁') (_ —→⟨ β-if₂ ⟩ _ ∎)) VN'

-- TODO
-- adequacy
-- logical equivalence implies contextual equivalence
postulate
  ≈-ctx : ∀ {Γ : Context n} {A M N}
    → Γ ⊢ M ≈ N ⦂ A
      -----------------
    → Γ ⊢ M ≈ctx N ⦂ A
