module safety where

open import stlc
open import prop
open import subst

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Relation.Nullary using (¬_; contradiction; Dec; yes; no)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)

-- reference: https://github.com/tmoux/logical-relations/blob/main/theories/Stlc.v

private
  variable
    n m : ℕ

Safe : Term 0 → Set
Safe M = ∀ M' → M —→* M' → Value M' ⊎ ∃[ M'' ] (M' —→ M'')

Irred : Term 0 → Set
Irred M = ∀ M' → ¬ (M —→ M')

𝒱⟦_⟧ : Type → Term 0 → Set
ℰ⟦_⟧ : Type → Term 0 → Set

𝒱⟦ bool  ⟧ true  = ⊤
𝒱⟦ bool  ⟧ false = ⊤
𝒱⟦ A ⇒ B ⟧ (ƛ M) = ∀ N → 𝒱⟦ A ⟧ N → ℰ⟦ B ⟧ (M [ N ])
𝒱⟦ _     ⟧ _     = ⊥

ℰ⟦ A ⟧ M = ∀ M' → ((M —→* M') × Irred M') → 𝒱⟦ A ⟧ M'

𝒢⟦_⟧ : Context n → (Fin n → Term 0) → Set
𝒢⟦ Γ ⟧ σ = ∀ {x A} → Γ ∋ x ⦂ A → 𝒱⟦ A ⟧ (σ x)

_⊨_⦂_ : Context n → Term n → Type → Set
Γ ⊨ M ⦂ A = ∀ σ → 𝒢⟦ Γ ⟧ σ → ℰ⟦ A ⟧ (subst σ M)

M→*M'-irred : ∀ {M M'} → M —→* M' → Irred M → M ≡ M'
M→*M'-irred (_ ∎)             irredM = refl
M→*M'-irred (_ —→⟨ x ⟩ M→*M') irredM = ⊥-elim (irredM _ x)

𝒱-irred : ∀ {M A} → 𝒱⟦ A ⟧ M → Irred M
𝒱-irred {M = true}  {A = bool}  VM M' ()
𝒱-irred {M = false} {A = bool}  VM M' ()
𝒱-irred {M = ƛ M}   {A = A ⇒ B} VM M' ()

𝒱-value : ∀ {M A} → 𝒱⟦ A ⟧ M → Value M
𝒱-value {M = true}  {A = bool}  VM = V-true
𝒱-value {M = false} {A = bool}  VM = V-false
𝒱-value {M = ƛ M}   {A = A ⇒ B} VM = V-abs

value? : (M : Term 0) → Dec (Value M)
value? (ƛ M)      = yes V-abs
value? (M · N)    = no λ ()
value? true       = yes V-true
value? false      = yes V-false
value? (if L M N) = no λ ()

reducible? : (M : Term 0) → Dec (∃[ M' ] M —→ M')
reducible? (ƛ M) = no λ ()
reducible? (M · N) with reducible? M
... | yes (M' , M→M') = yes (M' · N , ξ-app₁ M→M')
reducible? ((ƛ M) · N) | no irredM with reducible? N | value? N
... | yes (N' , N→N') | _ = yes ((ƛ M) · N' , ξ-app₂ V-abs N→N')
... | no  irredN      | yes VN = yes ((M [ N ]) , β-abs VN)
... | no  irredN      | no ¬VN = no λ { (_ , ξ-app₂ x N→N') → irredN (_ , N→N') ; (_ , β-abs x) → ¬VN x }
reducible? (M₁ · M₂ · N) | no irredM = no λ { (_ , ξ-app₁ M→M') → irredM (_ , M→M') }
reducible? (true · N) | no irredM with reducible? N
... | yes (N' , N→N') = yes (true · N' , ξ-app₂ V-true N→N')
... | no irredN = no λ { (_ , ξ-app₂ x N→N') → irredN (_ , N→N') }
reducible? (false · N) | no irredM  with reducible? N
... | yes (N' , N→N') = yes (false · N' , ξ-app₂ V-false N→N')
... | no irredN = no λ { (_ , ξ-app₂ x N→N') → irredN (_ , N→N') }
reducible? (if M₁ M₂ M₃ · N) | no irredM = no λ { (_ , ξ-app₁ M→M') → irredM (_ , M→M') }
reducible? true = no λ ()
reducible? false = no λ ()
reducible? (if L M N) with reducible? L
... | yes (M' , M→M') = yes (if M' M N , ξ-if M→M')
... | no  irredM with L
... | ƛ L₁ = no λ { (_ , ξ-if if→if') → irredM (_ , if→if') }
... | L₁ · L₂ = no λ { (_ , ξ-if if→if') → irredM (_ , if→if') }
... | true = yes (M , β-if₁)
... | false = yes (N , β-if₂)
... | if L₁ L₂ L₃ = no λ { (_ , ξ-if if→if') → irredM (_ , if→if') }

V-irred : ∀ {M} → Value M → Irred M
V-irred V-abs M' ()
V-irred V-true M' ()
V-irred V-false M' ()

appL-step : ∀ {M N V} → M · N —→* V → Irred V → ∃[ M' ] ((M —→* M') × Irred M')
appL-step ((M · N) ∎) ir = M , (M ∎) , λ { M' x → ir (M' · N) (ξ-app₁ x) }
appL-step ((M · N) —→⟨ ξ-app₁ x ⟩ st) ir with M' , stM' , irM' ← appL-step st ir = M' , step—→ M stM' x , irM'
appL-step ((M · N) —→⟨ ξ-app₂ x x₁ ⟩ st) ir = appL-step st ir
appL-step (((ƛ M) · N) —→⟨ β-abs x ⟩ st) ir = ƛ M , (ƛ M ∎) , λ { M' () }

appR-step : ∀ {M N V} → (ƛ M) · N —→* V → Irred V → ∃[ N' ] ((N —→* N') × Irred N')
appR-step (((ƛ M) · N) ∎) ir = N , (N ∎) , λ { M' x → ir ((ƛ M) · M') (ξ-app₂ V-abs x) }
appR-step (((ƛ M) · N) —→⟨ ξ-app₂ x x₁ ⟩ st) ir with N' , stN' , irN' ← appR-step st ir = N' , step—→ N stN' x₁ , irN'
appR-step (((ƛ M) · N) —→⟨ β-abs x ⟩ st) ir = N , (N ∎) , V-irred x

if-step : ∀ {L M N V} → if L M N —→* V → Irred V → ∃[ L' ] ((L —→* L') × Irred L')
if-step ((if L M N) ∎) ir = L , (L ∎) , (λ M' z → ir (if M' M N) (ξ-if z))
if-step ((if L M N) —→⟨ ξ-if x ⟩ st) ir with L'' , stL'' , irL'' ← if-step st ir = L'' , (L —→⟨ x ⟩ stL'') , irL''
if-step ((if true M N) —→⟨ β-if₁ ⟩ st) ir = true , (true ∎) , λ { x () }
if-step ((if false M N) —→⟨ β-if₂ ⟩ st) ir = false , (false ∎) , λ {x () }

𝒱⟦bool⟧-C : ∀ {M} → 𝒱⟦ bool ⟧ M → M ≡ true ⊎ M ≡ false
𝒱⟦bool⟧-C {M = true} VM = inj₁ refl
𝒱⟦bool⟧-C {M = false} VM = inj₂ refl

𝒱⟦abs⟧-C : ∀ {M A B} → 𝒱⟦ A ⇒ B ⟧ M → ∃[ N ] (M ≡ ƛ N)
𝒱⟦abs⟧-C {M = ƛ M} VM = M , refl

-- adequacy
⊨-safe : ∀ {M A} → ∅ ⊨ M ⦂ A → Safe M
⊨-safe ⊨M M' M→*M' with reducible? M'
... | yes M'→M'' = inj₂ M'→M''
... | no ¬M'→M'' = inj₁ (𝒱-value (⊨M ids (λ ()) M' (⟪id⟫M≡M , irredM')))
  where
    ⟪id⟫M≡M = Eq.subst (λ z → z —→* M') (Eq.sym sub-id) M→*M'
    irredM' = λ M'' z → ¬M'→M'' (M'' , z)

-- fundamental property
⊢-⊨ : ∀ {Γ : Context n} {M A} → Γ ⊢ M ⦂ A → Γ ⊨ M ⦂ A
⊢-⊨ {Γ = Γ ,- B} (⊢var x) σ GG M' (M→*M' , irredM')
  with refl ← M→*M'-irred M→*M' (𝒱-irred (GG x)) = GG x
⊢-⊨ {M = ƛ M} {A = A ⇒ B} (⊢abs ⊢M) σ GG M' (((ƛ ⟪σ⟫M) ∎) , irredM') N VN M'' (st , ir)
  = ⊢-⊨ ⊢M (N • σ) (λ { Z → VN ; (S x) → GG x }) M'' (st' , ir)
  where
    st' : subst (N • σ) M —→* M''
    st' rewrite Eq.sym (sub-ext-sub {σ = σ} {M = M} {N = N}) = st
⊢-⊨ {M = M · N} (⊢app {A = A} {B = B} ⊢M ⊢N) σ GG M' (M→*M' , irredM')
  with L' , σL→L' , il ← appL-step M→*M' irredM'
  with M'' , refl ← 𝒱⟦abs⟧-C (⊢-⊨ ⊢M σ GG L' (σL→L' , il))
  with LM' , ssl , ssr ← confluence M→*M' (—→*-trans (appL-cong σL→L') ((ƛ M'') · subst σ N ∎))
  with refl ← M→*M'-irred ssl irredM'
  with R' , σR→R' , ir ← appR-step ssr irredM'
  with VN ← ⊢-⊨ ⊢N σ GG R' (σR→R' , ir)
  with M'' , stl , str ← confluence M→*M' (—→*-trans (appL-cong σL→L') (—→*-trans (appR-cong V-abs σR→R') ((ƛ M'') · R' —→⟨ β-abs (𝒱-value VN) ⟩ _ ∎)))
  with refl ← M→*M'-irred stl irredM'
  = ⊢-⊨ ⊢M σ GG L' (σL→L' , il) R' VN M' (str , irredM')
⊢-⊨ ⊢true σ GG M' (M→*M' , irredM')
  with refl ← M→*M'-irred M→*M' (λ { _ () }) = tt
⊢-⊨ ⊢false σ GG M' (M→*M' , irredM')
  with refl ← M→*M'-irred M→*M' (λ { _ () }) = tt
⊢-⊨ {M = if L M N} (⊢if ⊢L ⊢M ⊢N) σ GG M' (M→*M' , irredM')
  with L' , σL→L' , il ← if-step M→*M' irredM'
  with 𝒱⟦bool⟧-C (⊢-⊨ ⊢L σ GG L' (σL→L' , il))
... | inj₁ refl
  with M'' , stl , str ← confluence M→*M' (—→*-trans (if-cong σL→L') (_ —→⟨ β-if₁ ⟩ subst σ M ∎))
  with refl ← M→*M'-irred stl irredM'
  = ⊢-⊨ ⊢M σ GG M' (str , irredM')
... | inj₂ refl
  with M'' , stl , str ← confluence M→*M' (—→*-trans (if-cong σL→L') (_ —→⟨ β-if₂ ⟩ subst σ N ∎))
  with refl ← M→*M'-irred stl irredM'
  = ⊢-⊨ ⊢N σ GG M' (str , irredM')
