module subst where

open import stlc

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong-app)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Relation.Nullary using (¬_; contradiction)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Function.Base using (id; _∘_)

-- copied from: https://plfa.github.io/Substitution/

private
  variable
    n m r s : ℕ

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      ------------------------
    → f ≡ g

-----------------
-- definitions --
-----------------

Rename : ℕ → ℕ → Set
Rename n m = Fin n → Fin m

Subst : ℕ → ℕ → Set
Subst n m = Fin n → Term m

⟪_⟫ : Subst n m → Term n → Term m
⟪ σ ⟫ = λ M → subst σ M

ids : Subst n n
ids x = ` x

↑ : Subst n (suc n)
↑ x = ` (fs x)

infixr 6 _•_

_•_ : Term m → Subst n m → Subst (suc n) m
(M • σ) fz     = M
(M • σ) (fs x) = σ x

infixr 5 _⨟_

_⨟_ : Subst n m → Subst m r → Subst n r
σ ⨟ τ = ⟪ τ ⟫ ∘ σ

ren : Rename n m → Subst n m
ren ρ = ids ∘ ρ

ext-subst : Subst n m → Term m → Subst (suc n) m
ext-subst σ M = subst (subst-zero M) ∘ exts σ

------------
-- lemmas --
------------

sub-head : ∀ {M} {σ : Subst n m} → ⟪ M • σ ⟫ (` fz) ≡ M
sub-head = refl

sub-tail : ∀ {M} {σ : Subst n m} → (↑ ⨟ M • σ) ≡ σ
sub-tail = extensionality λ x → refl

sub-η : ∀ {σ : Subst (suc n) m} → (⟪ σ ⟫ (` fz) • (↑ ⨟ σ)) ≡ σ
sub-η {σ = σ} = extensionality λ x → lemma
   where
     lemma : ∀ {x} → ((⟪ σ ⟫ (` fz)) • (↑ ⨟ σ)) x ≡ σ x
     lemma {x = fz} = refl
     lemma {x = fs x} = refl

Z-shift : ((` fz) • ↑) ≡ ids {n = (suc n)}
Z-shift = extensionality lemma
   where
     lemma : (x : Fin (suc n)) → ((` fz) • ↑) x ≡ ids x
     lemma fz = refl
     lemma (fs y) = refl

sub-idL : ∀ {σ : Subst n m} → ids ⨟ σ ≡ σ
sub-idL = extensionality λ x → refl

sub-dist :  ∀ {M} {σ : Subst n m} {τ : Subst m r}
         → ((M • σ) ⨟ τ) ≡ ((⟪ τ ⟫ M) • (σ ⨟ τ))
sub-dist {n = n} {M = M} {σ} {τ} = extensionality λ x → lemma {x = x}
  where
    lemma : ∀ {x : Fin (suc n)} → ((M • σ) ⨟ τ) x ≡ ((subst τ M) • (σ ⨟ τ)) x
    lemma {x = fz} = refl
    lemma {x = fs x} = refl

sub-app : ∀ {L M : Term n} {σ : Subst n m} → ⟪ σ ⟫ (L · M)  ≡ (⟪ σ ⟫ L) · (⟪ σ ⟫ M)
sub-app = refl

cong-ext : ∀ {ρ ρ′ : Rename n m} → ρ ≡ ρ′ → ext ρ ≡ ext ρ′
cong-ext {n} {ρ = ρ} {ρ′} rr = extensionality λ x → lemma {x = x}
  where
    lemma : ∀ {x : Fin (suc n)} → ext ρ x ≡ ext ρ′ x
    lemma {fz} = refl
    lemma {fs y} = cong fs (cong-app rr y)

cong-rename : ∀ {ρ ρ' : Rename n m} {M : Term n} → ρ ≡ ρ' → rename ρ M ≡ rename ρ' M
cong-rename {M = ` x} rr = cong `_ (cong-app rr x)
cong-rename {ρ = ρ} {ρ'} {M = ƛ M} rr
  rewrite cong-rename {ρ = ext ρ} {ρ' = ext ρ'} {M = M} (cong-ext rr)
  = refl
cong-rename {M = M · N} rr
  rewrite cong-rename {M = M} rr
  | cong-rename {M = N} rr
  = refl
cong-rename {M = true} rr = refl
cong-rename {M = false} rr = refl
cong-rename {M = if L M N} rr
  rewrite cong-rename {M = L} rr
  | cong-rename {M = M} rr
  | cong-rename {M = N} rr
  = refl

cong-exts : ∀ {σ σ' : Subst n m} → σ ≡ σ' → exts σ ≡ exts σ'
cong-exts {σ = σ}{σ'} ss = extensionality λ x → lemma {x = x}
   where
     lemma : ∀{x} → exts σ x ≡ exts σ' x
     lemma {fz} = refl
     lemma {fs x} = cong (rename fs) (cong-app ss x)

cong-sub : ∀ {σ σ' : Subst n m} {M M' : Term n}
  → σ ≡ σ' →  M ≡ M'
    ------------------------
  → subst σ M ≡ subst σ' M'
cong-sub {M = ` x} ss refl = cong-app ss x
cong-sub {σ = σ} {σ'} {M = ƛ M} ss refl
  rewrite cong-sub {σ = exts σ} {σ' = exts σ'} {M = M} (cong-exts ss) refl
  = refl
cong-sub {M = M · N} ss refl
  rewrite cong-sub {M = M} ss refl
  | cong-sub {M = N} ss refl
  = refl
cong-sub {M = true} ss refl = refl
cong-sub {M = false} ss refl = refl
cong-sub {M = if L M N} ss refl
  rewrite cong-sub {M = L} ss refl
  | cong-sub {M = M} ss refl
  | cong-sub {M = N} ss refl
  = refl

cong-sub-zero : ∀ {M M' : Term n} → M ≡ M' → subst-zero M ≡ subst-zero M'
cong-sub-zero mm' = extensionality λ x → cong (λ z → subst-zero z x) mm'

cong-cons : ∀ {M N : Term m} {σ τ : Subst n m}
  → M ≡ N → σ ≡ τ
    --------------------------------
  → (M • σ) ≡ (N • τ)
cong-cons {n = n} {M = M} {N} {σ} {τ} refl st = extensionality lemma
  where
    lemma : (x : Fin (suc n)) → (M • σ) x ≡ (M • τ) x
    lemma fz = refl
    lemma (fs x) = cong-app st x

cong-seq : ∀ {σ σ' : Subst n m} {τ τ' : Subst m r}
  → σ ≡ σ' → τ ≡ τ'
    --------------------
  → (σ ⨟ τ) ≡ (σ' ⨟ τ')
cong-seq {n = n} {σ = σ} {σ'} {τ} {τ'} ss' tt' = extensionality lemma
  where
    lemma : (x : Fin n) → (σ ⨟ τ) x ≡ (σ' ⨟ τ') x
    lemma x rewrite tt' | ss' = refl

ren-ext : ∀ {ρ : Rename n m} → ren (ext ρ) ≡ exts (ren ρ)
ren-ext {n = n} {ρ = ρ} = extensionality λ x → lemma {x = x}
  where
    lemma : ∀ {x : Fin (suc n)} → (ren (ext ρ)) x ≡ exts (ren ρ) x
    lemma {x = fz} = refl
    lemma {x = fs x} = refl

rename-subst-ren : ∀ {ρ : Rename n m} {M} → rename ρ M ≡ ⟪ ren ρ ⟫ M
rename-subst-ren {M = ` x} = refl
rename-subst-ren {ρ = ρ} {M = ƛ M}
  rewrite rename-subst-ren {ρ = ext ρ} {M = M}
  | cong-sub {M = M} (ren-ext {ρ = ρ}) refl
  = refl
rename-subst-ren {ρ = ρ} {M = M · N}
  rewrite rename-subst-ren {ρ = ρ} {M = M}
  | rename-subst-ren {ρ = ρ} {M = N}
  = refl
rename-subst-ren {M = true} = refl
rename-subst-ren {M = false} = refl
rename-subst-ren {ρ = ρ} {M = if L M N}
  rewrite rename-subst-ren {ρ = ρ} {M = L}
  | rename-subst-ren {ρ = ρ} {M = M}
  | rename-subst-ren {ρ = ρ} {M = N}
  = refl

ren-shift : ren {n = n} fs ≡ ↑
ren-shift {n = n} = extensionality λ x → lemma {x = x}
  where
    lemma : ∀ {x : Fin n} → ren fs x ≡ ↑ x
    lemma {x = fz} = refl
    lemma {x = fs x} = refl

rename-shift : ∀ {M : Term n} → rename fs M ≡ ⟪ ↑ ⟫ M
rename-shift {M = M}
  rewrite rename-subst-ren {ρ = fs} {M = M}
  | cong-sub{M = M} ren-shift refl
  = refl

exts-cons-shift : ∀ {σ : Subst n m} → exts σ ≡ (` fz • (σ ⨟ ↑))
exts-cons-shift = extensionality λ x → lemma {x = x}
  where
  lemma : ∀ {σ : Subst n m} {x : Fin (suc n)} → exts σ x ≡ (` fz • (σ ⨟ ↑)) x
  lemma {x = fz} = refl
  lemma {x = fs y} = rename-subst-ren

ext-cons-Z-shift : ∀ {ρ : Rename n m} → ren (ext ρ) ≡ (` fz • (ren ρ ⨟ ↑))
ext-cons-Z-shift {ρ = ρ}
  rewrite ren-ext {ρ = ρ}
  | exts-cons-shift {σ = ren ρ}
  = refl

subst-Z-cons-ids : ∀ {M : Term n} → subst-zero M ≡ (M • ids)
subst-Z-cons-ids = extensionality λ x → lemma {x = x}
  where
    lemma : ∀ {M : Term n} {x} → subst-zero M x ≡ (M • ids) x
    lemma {x = fz} = refl
    lemma {x = fs x} = refl

sub-abs : ∀ {σ : Subst n m} {N : Term (suc n)}
        → ⟪ σ ⟫ (ƛ N) ≡ ƛ ⟪ (` fz) • (σ ⨟ ↑) ⟫ N
sub-abs {σ = σ} {N = N}
  rewrite cong-sub {σ = exts σ} {M = N} exts-cons-shift refl
  = refl

exts-ids : exts ids ≡ ids {n = suc n}
exts-ids {n = n} = extensionality lemma
  where
    lemma : (x : Fin (suc n)) → exts ids x ≡ ids x
    lemma fz = refl
    lemma (fs x) = refl

sub-id : ∀ {M : Term n} → subst ids M ≡ M
sub-id {M = ` x} = refl
sub-id {M = ƛ M}
  rewrite cong-sub {M = M} exts-ids refl
  | sub-id {M = M}
  = refl
sub-id {M = M · N} rewrite sub-id {M = M} | sub-id {M = N} = refl
sub-id {M = true} = refl
sub-id {M = false} = refl
sub-id {M = if L M N}
  rewrite sub-id {M = L}
  | sub-id {M = M}
  | sub-id {M = N}
  = refl

rename-id : ∀ {M : Term n} → rename id M ≡ M
rename-id {M = M}
  rewrite rename-subst-ren {ρ = id} {M = M}
  | sub-id {M = M}
  = refl

sub-idR : ∀ {σ : Subst n m} → (σ ⨟ ids) ≡ σ
sub-idR {n = n} {σ = σ} = extensionality λ x → lemma {x = x}
  where
    lemma : {x : Fin n} → (σ ⨟ ids) x ≡ σ x
    lemma {x = x} rewrite sub-id {M = ` x} | sub-id {M = σ x} = refl

compose-ext : ∀ {ρ : Rename m r} {ρ' : Rename n m}
  → ((ext ρ) ∘ (ext ρ')) ≡ ext (ρ ∘ ρ')
compose-ext = extensionality λ x → lemma {x = x}
  where
    lemma : ∀ {ρ : Rename m r} {ρ' : Rename n m} {x : Fin (suc n)}
      → ((ext ρ) ∘ (ext ρ')) x ≡ ext (ρ ∘ ρ') x
    lemma {x = fz} = refl
    lemma {x = fs x} = refl

compose-rename : ∀ {M : Term n} {ρ : Rename m r} {ρ' : Rename n m}
  → rename ρ (rename ρ' M) ≡ rename (ρ ∘ ρ') M
compose-rename {M = ` x} = refl
compose-rename {M = ƛ M} {ρ} {ρ'} = cong ƛ_ G
  where
    G : rename (ext ρ) (rename (ext ρ') M) ≡ rename (ext (ρ ∘ ρ')) M
    G rewrite compose-rename {M = M} {ρ = ext ρ} {ρ' = ext ρ'}
      | cong-rename {M = M} (compose-ext {ρ = ρ} {ρ' = ρ'}) = refl
compose-rename {M = M · N} {ρ} {ρ'}
  rewrite compose-rename {M = M} {ρ} {ρ'}
  | compose-rename {M = N} {ρ} {ρ'}
  = refl
compose-rename {M = true} = refl
compose-rename {M = false} = refl
compose-rename {M = if L M N} {ρ} {ρ'}
  rewrite compose-rename {M = L} {ρ} {ρ'}
  | compose-rename {M = M} {ρ} {ρ'}
  | compose-rename {M = N} {ρ} {ρ'}
  = refl

commute-subst-rename : ∀ {M : Term n} {σ : Subst n m}
    {ρ₁ : Rename n (suc n)} {ρ₂ : Rename m (suc m)}
  → (∀ {x : Fin n} → exts σ (ρ₁ x) ≡ rename ρ₂ (σ x))
  → subst (exts σ) (rename ρ₁ M) ≡ rename ρ₂ (subst σ M)
commute-subst-rename {M = ` x} H = H
commute-subst-rename {n = n} {M = ƛ M} {σ} {ρ₁} {ρ₂} H =
  cong ƛ_ (commute-subst-rename {M = M} {exts σ} {ext ρ₁} {ext ρ₂} (λ {x} → H' {x}))
  where
     H' : ∀ {x : Fin (suc n)} → exts (exts σ) (ext ρ₁ x) ≡ rename (ext ρ₂) (exts σ x)
     H' {x = fz} = refl
     H' {x = fs x}
       rewrite cong (rename fs) (H {x = x})
       | compose-rename {M = σ x} {ρ = fs} {ρ' = ρ₂}
       | compose-rename {M = σ x} {ρ = ext ρ₂} {ρ' = fs}
       = refl
commute-subst-rename {M = M · N} {σ} {ρ₁} {ρ₂} H
  rewrite commute-subst-rename {M = M} {σ} {ρ₁} {ρ₂} H
  | commute-subst-rename {M = N} {σ} {ρ₁} {ρ₂} H
  = refl
commute-subst-rename {M = true} H = refl
commute-subst-rename {M = false} H = refl
commute-subst-rename {M = if L M N} {σ} {ρ₁} {ρ₂} H
  rewrite commute-subst-rename {M = L} {σ} {ρ₁} {ρ₂} H
  | commute-subst-rename {M = M} {σ} {ρ₁} {ρ₂} H
  | commute-subst-rename {M = N} {σ} {ρ₁} {ρ₂} H
  = refl

exts-seq : ∀ {σ₁ : Subst n m} {σ₂ : Subst m r}
  → (exts σ₁ ⨟ exts σ₂) ≡ exts (σ₁ ⨟ σ₂)
exts-seq {n = n} = extensionality λ x → lemma {x = x}
  where
    lemma : ∀ {x : Fin (suc n)} {σ₁ : Subst n m} {σ₂ : Subst m r}
      → (exts σ₁ ⨟ exts σ₂) x ≡ exts (σ₁ ⨟ σ₂) x
    lemma {x = fz} = refl
    lemma {x = fs x} {σ₁ = σ₁} {σ₂ = σ₂}
      rewrite commute-subst-rename {M = σ₁ x} {σ = σ₂} {ρ₁ = fs} {ρ₂ = fs} refl
      = refl

sub-sub : ∀ {M : Term n} {σ₁ : Subst n m} {σ₂ : Subst m r}
  → ⟪ σ₂ ⟫ (⟪ σ₁ ⟫ M) ≡ ⟪ σ₁ ⨟ σ₂ ⟫ M
sub-sub {M = ` x} = refl
sub-sub {M = ƛ M} {σ₁} {σ₂}
  rewrite sub-sub {M = M} {σ₁ = exts σ₁} {σ₂ = exts σ₂}
  | exts-seq {σ₁ = σ₁} {σ₂ = σ₂}
  = refl
sub-sub {M = M · N} {σ₁} {σ₂}
  rewrite sub-sub {M = M} {σ₁} {σ₂}
  | sub-sub {M = N} {σ₁} {σ₂}
  = refl
sub-sub {M = true} = refl
sub-sub {M = false} = refl
sub-sub {M = if L M N} {σ₁} {σ₂}
  rewrite sub-sub {M = L} {σ₁} {σ₂}
  | sub-sub {M = M} {σ₁} {σ₂}
  | sub-sub {M = N} {σ₁} {σ₂}
  = refl

rename-subst : ∀ {M : Term n} {ρ : Rename n m} {σ : Subst m r}
  → ⟪ σ ⟫ (rename ρ M) ≡ ⟪ σ ∘ ρ ⟫ M
rename-subst {M = M} {ρ} {σ}
  rewrite rename-subst-ren {ρ = ρ} {M = M}
  | sub-sub {M = M} {σ₁ = ren ρ} {σ₂ = σ}
  = refl

sub-assoc : ∀ {σ : Subst n m} {τ : Subst m r} {θ : Subst r s}
  → (σ ⨟ τ) ⨟ θ ≡ (σ ⨟ τ ⨟ θ)
sub-assoc {n = n} {σ = σ} {τ} {θ} = extensionality λ x → lemma {x = x}
  where
    lemma : ∀ {x : Fin n} → ((σ ⨟ τ) ⨟ θ) x ≡ (σ ⨟ τ ⨟ θ) x
    lemma {x} rewrite sub-sub {M = σ x} {σ₁ = τ} {σ₂ = θ} = refl

subst-zero-exts-cons : ∀ {σ : Subst n m} {M : Term m} → exts σ ⨟ subst-zero M ≡ (M • σ)
subst-zero-exts-cons {σ = σ} {M}
  rewrite cong-seq (exts-cons-shift {σ = σ}) (subst-Z-cons-ids {M = M})
  | sub-dist {M = ` fz} {σ = σ ⨟ ↑} {τ = M • ids}
  | sub-head {M = M} {σ = ids}
  | sub-assoc {σ = σ} {τ = ↑} {θ = (M • ids)}
  | sub-tail {M = M} {σ = ids}
  | sub-idR {σ = σ}
  = refl

subst-commute : ∀ {N : Term (suc n)} {M : Term n} {σ : Subst n m }
  → ⟪ exts σ ⟫ N [ ⟪ σ ⟫ M ] ≡ ⟪ σ ⟫ (N [ M ])
subst-commute {N = N} {M} {σ} =
  begin
    ⟪ exts σ ⟫ N [ ⟪ σ ⟫ M ]
  ≡⟨⟩
    ⟪ subst-zero (⟪ σ ⟫ M) ⟫ (⟪ exts σ ⟫ N)
  ≡⟨ cong-sub {M = ⟪ exts σ ⟫ N} subst-Z-cons-ids refl ⟩
    ⟪ ⟪ σ ⟫ M • ids ⟫ (⟪ exts σ ⟫ N)
  ≡⟨ sub-sub {M = N} ⟩
    ⟪ (exts σ) ⨟ ((⟪ σ ⟫ M) • ids) ⟫ N
  ≡⟨ cong-sub {M = N} (cong-seq exts-cons-shift refl) refl ⟩
    ⟪ (` fz • (σ ⨟ ↑)) ⨟ (⟪ σ ⟫ M • ids) ⟫ N
  ≡⟨ cong-sub {M = N} (sub-dist {M = ` fz}) refl ⟩
    ⟪ ⟪ ⟪ σ ⟫ M • ids ⟫ (` fz) • ((σ ⨟ ↑) ⨟ (⟪ σ ⟫ M • ids)) ⟫ N
  ≡⟨⟩
    ⟪ ⟪ σ ⟫ M • ((σ ⨟ ↑) ⨟ (⟪ σ ⟫ M • ids)) ⟫ N
  ≡⟨ cong-sub{M = N} (cong-cons refl (sub-assoc{σ = σ})) refl ⟩
    ⟪ ⟪ σ ⟫ M • (σ ⨟ ↑ ⨟ ⟪ σ ⟫ M • ids) ⟫ N
  ≡⟨ cong-sub{M = N} refl refl ⟩
    ⟪ ⟪ σ ⟫ M • (σ ⨟ ids) ⟫ N
  ≡⟨ cong-sub{M = N} (cong-cons refl (sub-idR{σ = σ})) refl ⟩
    ⟪ ⟪ σ ⟫ M • σ ⟫ N
  ≡⟨ cong-sub{M = N} (cong-cons refl (sub-idL{σ = σ})) refl ⟩
    ⟪ ⟪ σ ⟫ M • (ids ⨟ σ) ⟫ N
  ≡⟨ cong-sub{M = N} (sym sub-dist) refl ⟩
    ⟪ M • ids ⨟ σ ⟫ N
  ≡⟨ sym (sub-sub{M = N}) ⟩
    ⟪ σ ⟫ (⟪ M • ids ⟫ N)
  ≡⟨ cong ⟪ σ ⟫ (sym (cong-sub{M = N} subst-Z-cons-ids refl)) ⟩
    ⟪ σ ⟫ (N [ M ])
  ∎

rename-subst-commute : ∀ {N : Term (suc n)} {M : Term n} {ρ : Rename n m}
  → (rename (ext ρ) N) [ rename ρ M ] ≡ rename ρ (N [ M ])
rename-subst-commute {N = N} {M} {ρ} =
  begin
    (rename (ext ρ) N) [ rename ρ M ]
  ≡⟨ cong-sub (cong-sub-zero (rename-subst-ren{M = M}))
              (rename-subst-ren{M = N}) ⟩
    (⟪ ren (ext ρ) ⟫ N) [ ⟪ ren ρ ⟫ M ]
  ≡⟨ cong-sub refl (cong-sub{M = N} ren-ext refl) ⟩
    (⟪ exts (ren ρ) ⟫ N) [ ⟪ ren ρ ⟫ M ]
  ≡⟨ subst-commute{N = N} ⟩
    subst (ren ρ) (N [ M ])
  ≡⟨ sym (rename-subst-ren) ⟩
    rename ρ (N [ M ])
  ∎

_〔_〕 : Term (suc (suc n)) → Term n → Term (suc n)
_〔_〕 N M = subst (exts (subst-zero M)) N

substitution : ∀ {M : Term (suc (suc n))} {N : Term (suc n)} {L : Term n}
  → (M [ N ]) [ L ] ≡ (M 〔 L 〕) [ (N [ L ]) ]
substitution {M = M} {N = N} {L = L} =
   sym (subst-commute {N = M} {M = N} {σ = subst-zero L})

subst-zero-exts : ∀ {σ : Subst n m} {M : Term m} {x : Fin n}
  → (subst (subst-zero M) ∘ exts σ) (fs x) ≡ σ x
subst-zero-exts {σ = σ} {x = x} = cong-app (subst-zero-exts-cons {σ = σ}) (fs x)

ext-subst-cons : ∀ {M : Term m} {σ : Subst n m}
  → M • σ ≡ ext-subst σ M
ext-subst-cons {n = n} {M = M} {σ = σ} = extensionality λ x → lemma {x = x}
  where
    lemma : ∀ {x : Fin (suc n)} → (M • σ) x ≡ ext-subst σ M x
    lemma {x = fz} = refl
    lemma {x = fs x} rewrite subst-zero-exts {σ = σ} {M} {x} = refl

sub-ext-sub : ∀ {σ : Fin n → Term m} {M N}
  → subst (N • σ) M ≡ subst (exts σ) M [ N ]
sub-ext-sub {σ = σ} {M} {N}
  rewrite ext-subst-cons {M = N} {σ = σ}
  | sub-sub {M = M} {σ₁ = exts σ} {σ₂ = subst-zero N}
  = refl

rename-fs-commute : ∀ {ρ : Rename n m} {M}
  → rename fs (rename ρ M) ≡ rename (ext ρ) (rename fs M)
rename-fs-commute {ρ = ρ} {M = M} =
  begin
    rename fs (rename ρ M)
  ≡⟨ cong (rename fs) rename-subst-ren ⟩
    rename fs (⟪ ren ρ ⟫ M)
  ≡⟨ sym (commute-subst-rename {M = M} {σ = ren ρ} λ {x} → refl) ⟩
    ⟪ exts (ren ρ) ⟫ (rename fs M)
  ≡⟨ cong (λ x → ⟪ x ⟫ (rename fs M)) (sym ren-ext) ⟩
    ⟪ ren (ext ρ) ⟫ (rename fs M)
  ≡⟨ sym rename-subst-ren ⟩
    rename (ext ρ) (rename fs M)
  ∎
