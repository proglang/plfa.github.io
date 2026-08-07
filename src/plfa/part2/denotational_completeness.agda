module plfa.part2.denotational_completeness where

open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; proj₁; proj₂; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String; _≟_)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans) renaming (subst to ≡-subst)
open import Relation.Unary using (Pred; _∈_; Decidable)
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Nullary.Decidable using (Dec; yes; no; False; toWitnessFalse; ¬?)

-- Operators -------------------------------------------------------------------

infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_

infix  5 ƛ_
infixl 7 _·_
infix  8 `suc_
infix  9 `_
infix  9 S_

-- Syntax ----------------------------------------------------------------------

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

variable
  A B C : Type
  Γ Δ : Context

-- Variable lookup (as before)
data _∋_ : Context → Type → Set where
  Z : ∀ {Γ} → Γ , A ∋ A
  S_ : ∀ {Γ} → Γ ∋ A → Γ , B ∋ A

-- Terms and typing
-- Same as before, except that we remove `μ` and replace `case` by `recnat`.
data _⊢_ : Context → Type → Set where
  `_ : ∀ {Γ A}
    → Γ ∋ A
    → Γ ⊢ A
  ƛ_  : ∀ {Γ A B}
    → Γ , A ⊢ B
    → Γ ⊢ A ⇒ B
  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
    → Γ ⊢ B
  `zero : ∀ {Γ}
    → Γ ⊢ `ℕ
  `suc_ : ∀ {Γ}
    → Γ ⊢ `ℕ
    → Γ ⊢ `ℕ
  recnat : ∀ {Γ A}
    → Γ ⊢ `ℕ
    → Γ ⊢ A
    → Γ ⊢ `ℕ ⇒ A ⇒ A
    → Γ ⊢ A

-- Denotational Semantics ------------------------------------------------------

𝓣⟦_⟧ : Type → Set
𝓣⟦ A ⇒ B ⟧ = 𝓣⟦ A ⟧ → 𝓣⟦ B ⟧
𝓣⟦ `ℕ ⟧ = ℕ

𝓒⟦_⟧ : Context → Set
𝓒⟦ Γ ⟧ = ∀ A → Γ ∋ A → 𝓣⟦ A ⟧

extc : 𝓒⟦ Γ ⟧ → 𝓣⟦ A ⟧ → 𝓒⟦ Γ , A ⟧
extc γ a _ Z = a
extc γ a _ (S x) = γ _ x

recnat′ : ∀ {X : Set} → ℕ → (x₀ : X) → (sₛ : ℕ → X → X) → X
recnat′ zero x₀ xₛ = x₀
recnat′ (suc n) x₀ xₛ = xₛ n (recnat′ n x₀ xₛ)


𝓔⟦_⟧ : Γ ⊢ A → (𝓒⟦ Γ ⟧ → 𝓣⟦ A ⟧)
𝓔⟦ ` x ⟧ γ             = γ _ x
𝓔⟦ ƛ M ⟧ γ             = λ v → 𝓔⟦ M ⟧ (extc γ v)
𝓔⟦ M · M₁ ⟧ γ          = 𝓔⟦ M ⟧ γ (𝓔⟦ M₁ ⟧ γ)
𝓔⟦ `zero ⟧ γ           = zero
𝓔⟦ `suc M ⟧ γ          = suc (𝓔⟦ M ⟧ γ)
𝓔⟦ recnat M M₁ M₂ ⟧ γ  = recnat′ (𝓔⟦ M ⟧ γ) (𝓔⟦ M₁ ⟧ γ) (𝓔⟦ M₂ ⟧ γ)

-- Small-Step Semantics --------------------------------------------------------

-- Renamings

Ren : Context → Context → Set
Ren Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

extr : Ren Γ Δ → Ren (Γ , A) (Δ , A)
extr ρ Z = Z
extr ρ (S x) = S (ρ x)

rename : ∀ {Γ Δ} → Ren Γ Δ → Γ ⊢ A → Δ ⊢ A
rename ρ (` x) = ` (ρ x)
rename ρ (ƛ ⊢A) = ƛ rename (extr ρ) ⊢A
rename ρ (⊢A · ⊢A₁) = (rename ρ ⊢A) · (rename ρ ⊢A₁)
rename ρ `zero = `zero
rename ρ (`suc ⊢A) = `suc (rename ρ ⊢A)
rename ρ (recnat ⊢A ⊢A₁ ⊢A₂) = recnat (rename ρ ⊢A) (rename ρ ⊢A₁) (rename ρ ⊢A₂)

-- Substitutions

Sub : Context → Context → Set
Sub Γ Δ  = ∀ {A} → Γ ∋ A → Δ ⊢ A

exts : Sub Γ Δ → Sub (Γ , A) (Δ , A)
exts σ Z = ` Z
exts σ (S x) = rename S_ (σ x)

subst : ∀ {Γ Δ} → Sub Γ Δ → Γ ⊢ A → Δ ⊢ A
subst σ (` x) = σ x
subst σ (ƛ ⊢A) = ƛ subst (exts σ) ⊢A
subst σ (⊢A · ⊢A₁) = (subst σ ⊢A) · (subst σ ⊢A₁)
subst σ `zero = `zero
subst σ (`suc ⊢A) = `suc (subst σ ⊢A)
subst σ (recnat ⊢A ⊢A₁ ⊢A₂) = recnat (subst σ ⊢A) (subst σ ⊢A₁) (subst σ ⊢A₂)

-- Singleton Substitution

σ₀ : (M : Γ ⊢ B) → Sub (Γ , B) Γ
σ₀ M Z     = M
σ₀ M (S x) = ` x

_[_] : ∀ {Γ A B} → Γ , B ⊢ A → Γ ⊢ B → Γ ⊢ A
_[_] {Γ} {A} {B} N M = subst (σ₀ M) N

-- Values

data Value  {Γ} : ∀ {A} → Γ ⊢ A → Set where
  ƛ_    : (N : Γ , A ⊢ B) → Value (ƛ N)
  `zero : Value `zero
  `suc_ : ∀ {V : Γ ⊢ `ℕ} → Value V → Value (`suc V)

-- Reduction Relation

infix 2 _⟶_

data _⟶_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L ⟶ L′
    → L · M ⟶ L′ · M
  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M ⟶ M′
    → V · M ⟶ V · M′
  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
    → (ƛ N) · W ⟶ N [ W ]
  ξ-suc : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
    → M ⟶ M′
    → `suc M ⟶ `suc M′
  ξ-recnat : ∀ {Γ A} {L L′ : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ  ⊢ `ℕ ⇒ A ⇒ A}
    → L ⟶ L′
    → recnat L M N ⟶ recnat L′ M N
  β-zero :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ ⊢ `ℕ ⇒ A ⇒ A}
    → recnat `zero M N ⟶ M
  β-suc : ∀ {Γ A} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ ⊢ `ℕ ⇒ A ⇒ A}
    → Value V
    → recnat (`suc V) M N ⟶ N · V · recnat V M N

-- Relation between small-step and denotational semantics -------------------------

postulate
  ext : ∀ {A : Set}{B : A → Set} {f g : (a : A) → B a} → (∀ x → f x ≡ g x) → f ≡ g

𝓡⟦_⟧ : Ren Γ Δ → 𝓒⟦ Δ ⟧ → 𝓒⟦ Γ ⟧
𝓡⟦ ρ ⟧ δ _ x = δ _ (ρ x)

extc-ρ : ∀ {v : 𝓣⟦ A ⟧} (δ : 𝓒⟦ Δ ⟧) (ρ : Ren Γ Δ)
  → extc (𝓡⟦ ρ ⟧ δ) v ≡ 𝓡⟦ extr ρ ⟧ (extc δ v)
extc-ρ δ ρ = ext λ B → ext λ{ Z → refl ; (S x) → refl }

sound-ren : ∀ (M : Γ ⊢ A) (δ : 𝓒⟦ Δ ⟧) (ρ : Ren Γ Δ)
  → 𝓔⟦ M ⟧ (𝓡⟦ ρ ⟧ δ) ≡ 𝓔⟦ rename ρ M ⟧ δ
sound-ren (` x) δ ρ = refl
sound-ren (ƛ M) δ ρ = ext (λ v → trans (cong 𝓔⟦ M ⟧ (extc-ρ δ ρ)) (sound-ren M (extc δ v) (extr ρ)))
sound-ren (M · M₁) δ ρ rewrite sound-ren M δ ρ | sound-ren M₁ δ ρ = refl
sound-ren `zero δ ρ = refl
sound-ren (`suc M) δ ρ  rewrite sound-ren M δ ρ = refl
sound-ren (recnat M M₁ M₂) δ ρ rewrite sound-ren M δ ρ | sound-ren M₁ δ ρ | sound-ren M₂ δ ρ = refl

--      Sub Γ Δ → Sub Δ ∅ → Sub Γ ∅
𝓢⟦_⟧ : Sub Γ Δ → 𝓒⟦ Δ ⟧ → 𝓒⟦ Γ ⟧
𝓢⟦ σ ⟧ δ _ x = 𝓔⟦ σ x ⟧ δ

extc-exts : ∀ {v : 𝓣⟦ A ⟧} → (σ : Sub Γ Δ) (δ : 𝓒⟦ Δ ⟧)
  → extc {A = A} (𝓢⟦ σ ⟧ δ) v ≡ 𝓢⟦ exts σ ⟧ (extc {A = A} δ v)
extc-exts {v = v} σ δ = ext λ A → ext λ where
  Z     → refl
  (S x) → sound-ren (σ x) (extc δ v) S_

sound-sub : (M : Γ ⊢ A) (σ : Sub Γ Δ) (δ : 𝓒⟦ Δ ⟧)
  → 𝓔⟦ M ⟧ (𝓢⟦ σ ⟧ δ) ≡ 𝓔⟦ subst σ M ⟧ δ
sound-sub (` x) σ δ = refl
sound-sub (ƛ M) σ δ = ext λ v → trans (cong (𝓔⟦ M ⟧) (extc-exts σ δ) )
                                      (sound-sub M (exts σ) (extc δ v))
sound-sub (M · M₁) σ δ rewrite sound-sub M σ δ | sound-sub M₁ σ δ = refl
sound-sub `zero σ δ = refl
sound-sub (`suc M) σ δ = cong suc (sound-sub M σ δ)
sound-sub (recnat M M₁ M₂) σ δ rewrite sound-sub M σ δ | sound-sub M₁ σ δ | sound-sub M₂ σ δ = refl

extc-σ₀ : (γ  : 𝓒⟦ Γ ⟧) (W  : Γ ⊢ A) → extc γ (𝓔⟦ W ⟧ γ) ≡ 𝓢⟦ σ₀ W ⟧ γ
extc-σ₀ γ W = ext λ B → ext λ{ Z → refl ; (S x) → refl}

sound⟶ : ∀ {M N : Γ ⊢ A} → M ⟶ N → (γ : 𝓒⟦ Γ ⟧) → 𝓔⟦ M ⟧ γ ≡ 𝓔⟦ N ⟧ γ
sound⟶ (ξ-·₁ M⟶N) γ              rewrite sound⟶ M⟶N γ = refl
sound⟶ (ξ-·₂ x M⟶N) γ            rewrite sound⟶ M⟶N γ = refl
sound⟶ (β-ƛ {N = N}{W = W} v) γ  = trans (cong (𝓔⟦ N ⟧) (extc-σ₀ γ W))
                                         (sound-sub N (σ₀ W) γ)
sound⟶ (ξ-suc M⟶N) γ             rewrite sound⟶ M⟶N γ = refl
sound⟶ (ξ-recnat M⟶N) γ          rewrite sound⟶ M⟶N γ = refl
sound⟶ β-zero γ = refl
sound⟶ (β-suc x) γ = refl

-- Completeness ----------------------------------------------------------------


infix  2 _⟶*_
infixr 5 _∷_
infixr 5 _++_

data _⟶*_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
  ∎ : ∀ {Γ A} {M : Γ ⊢ A}
    → M ⟶* M
  _∷_ : ∀ {Γ A} {L M N : Γ ⊢ A}
    → L ⟶ M
    → M ⟶* N
    → L ⟶* N

_++_ : ∀ {M N P : Γ ⊢ A} → M ⟶* N → N ⟶* P → M ⟶* P
∎ ++ N⟶*P = N⟶*P
(L⟶M ∷ M⟶*N) ++ N⟶*P = L⟶M ∷ (M⟶*N ++ N⟶*P)

-- The ξ-rules lift to multi-step reduction.

ξ*-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
  → L ⟶* L′
  → L · M ⟶* L′ · M
ξ*-·₁ ∎ = ∎
ξ*-·₁ (L⟶L″ ∷ L″⟶*L′) = ξ-·₁ L⟶L″ ∷ ξ*-·₁ L″⟶*L′

ξ*-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
  → Value V
  → M ⟶* M′
  → V · M ⟶* V · M′
ξ*-·₂ v ∎ = ∎
ξ*-·₂ v (M⟶M″ ∷ M″⟶*M′) = ξ-·₂ v M⟶M″ ∷ ξ*-·₂ v M″⟶*M′

ξ*-suc : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
  → M ⟶* M′
  → `suc M ⟶* `suc M′
ξ*-suc ∎ = ∎
ξ*-suc (M⟶M″ ∷ M″⟶*M′) = ξ-suc M⟶M″ ∷ ξ*-suc M″⟶*M′

ξ*-recnat : ∀ {Γ A} {L L′ : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ ⊢ `ℕ ⇒ A ⇒ A}
  → L ⟶* L′
  → recnat L M N ⟶* recnat L′ M N
ξ*-recnat ∎ = ∎
ξ*-recnat (L⟶L″ ∷ L″⟶*L′) = ξ-recnat L⟶L″ ∷ ξ*-recnat L″⟶*L′

-- Numerals

-- The semantic value n : ℕ is represented by the numeral `suc (... (`zero)).

numeral : ∀ {Γ} → ℕ → Γ ⊢ `ℕ
numeral zero    = `zero
numeral (suc n) = `suc numeral n

numeral-Value : ∀ {Γ} (n : ℕ) → Value {Γ} (numeral n)
numeral-Value zero    = `zero
numeral-Value (suc n) = `suc numeral-Value n

numeral-subst : ∀ {n}{σ : Sub Γ Δ} → numeral n ≡ subst σ (numeral n)
numeral-subst {n = zero} = refl
numeral-subst {n = suc n} = cong `suc_ numeral-subst

-- Properties of Renaming and Substitution

variable
  Θ : Context

rename-cong : ∀ {ρ ρ′ : Ren Γ Δ}
  → (∀ {C} (x : Γ ∋ C) → ρ x ≡ ρ′ x)
  → (M : Γ ⊢ A)
  → rename ρ M ≡ rename ρ′ M
rename-cong eq (` x) = cong `_ (eq x)
rename-cong eq (ƛ M) = cong ƛ_ (rename-cong (λ{ Z → refl ; (S x) → cong S_ (eq x) }) M)
rename-cong eq (M · M₁) rewrite rename-cong eq M | rename-cong eq M₁ = refl
rename-cong eq `zero = refl
rename-cong eq (`suc M) = cong `suc_ (rename-cong eq M)
rename-cong eq (recnat M M₁ M₂)
  rewrite rename-cong eq M | rename-cong eq M₁ | rename-cong eq M₂ = refl

rename-rename : ∀ (ρ : Ren Γ Δ) (ρ′ : Ren Δ Θ) (M : Γ ⊢ A)
  → rename ρ′ (rename ρ M) ≡ rename (ρ′ ∘ ρ) M
rename-rename ρ ρ′ (` x) = refl
rename-rename ρ ρ′ (ƛ M) = cong ƛ_ (trans (rename-rename (extr ρ) (extr ρ′) M)
                                          (rename-cong (λ{ Z → refl ; (S x) → refl }) M))
rename-rename ρ ρ′ (M · M₁)
  rewrite rename-rename ρ ρ′ M | rename-rename ρ ρ′ M₁ = refl
rename-rename ρ ρ′ `zero = refl
rename-rename ρ ρ′ (`suc M) = cong `suc_ (rename-rename ρ ρ′ M)
rename-rename ρ ρ′ (recnat M M₁ M₂)
  rewrite rename-rename ρ ρ′ M | rename-rename ρ ρ′ M₁ | rename-rename ρ ρ′ M₂ = refl

subst-cong : ∀ {σ σ′ : Sub Γ Δ}
  → (∀ {C} (x : Γ ∋ C) → σ x ≡ σ′ x)
  → (M : Γ ⊢ A)
  → subst σ M ≡ subst σ′ M
subst-cong eq (` x) = eq x
subst-cong eq (ƛ M) = cong ƛ_ (subst-cong (λ{ Z → refl ; (S x) → cong (rename S_) (eq x) }) M)
subst-cong eq (M · M₁) rewrite subst-cong eq M | subst-cong eq M₁ = refl
subst-cong eq `zero = refl
subst-cong eq (`suc M) = cong `suc_ (subst-cong eq M)
subst-cong eq (recnat M M₁ M₂)
  rewrite subst-cong eq M | subst-cong eq M₁ | subst-cong eq M₂ = refl

subst-rename : ∀ (ρ : Ren Γ Δ) (σ : Sub Δ Θ) (M : Γ ⊢ A)
  → subst σ (rename ρ M) ≡ subst (σ ∘ ρ) M
subst-rename ρ σ (` x) = refl
subst-rename ρ σ (ƛ M) = cong ƛ_ (trans (subst-rename (extr ρ) (exts σ) M)
                                        (subst-cong (λ{ Z → refl ; (S x) → refl }) M))
subst-rename ρ σ (M · M₁)
  rewrite subst-rename ρ σ M | subst-rename ρ σ M₁ = refl
subst-rename ρ σ `zero = refl
subst-rename ρ σ (`suc M) = cong `suc_ (subst-rename ρ σ M)
subst-rename ρ σ (recnat M M₁ M₂)
  rewrite subst-rename ρ σ M | subst-rename ρ σ M₁ | subst-rename ρ σ M₂ = refl

rename-subst : ∀ (σ : Sub Γ Δ) (ρ : Ren Δ Θ) (M : Γ ⊢ A)
  → rename ρ (subst σ M) ≡ subst (rename ρ ∘ σ) M
rename-subst σ ρ (` x) = refl
rename-subst σ ρ (ƛ M) = cong ƛ_ (trans (rename-subst (exts σ) (extr ρ) M)
                                        (subst-cong (λ{ Z → refl
                                                      ; (S x) → trans (rename-rename S_ (extr ρ) (σ x))
                                                                      (sym (rename-rename ρ S_ (σ x))) }) M))
rename-subst σ ρ (M · M₁)
  rewrite rename-subst σ ρ M | rename-subst σ ρ M₁ = refl
rename-subst σ ρ `zero = refl
rename-subst σ ρ (`suc M) = cong `suc_ (rename-subst σ ρ M)
rename-subst σ ρ (recnat M M₁ M₂)
  rewrite rename-subst σ ρ M | rename-subst σ ρ M₁ | rename-subst σ ρ M₂ = refl

subst-subst : ∀ (σ : Sub Γ Δ) (τ : Sub Δ Θ) (M : Γ ⊢ A)
  → subst τ (subst σ M) ≡ subst (subst τ ∘ σ) M
subst-subst σ τ (` x) = refl
subst-subst σ τ (ƛ M) = cong ƛ_ (trans (subst-subst (exts σ) (exts τ) M)
                                       (subst-cong (λ{ Z → refl
                                                     ; (S x) → trans (subst-rename S_ (exts τ) (σ x))
                                                                     (sym (rename-subst τ S_ (σ x))) }) M))
subst-subst σ τ (M · M₁)
  rewrite subst-subst σ τ M | subst-subst σ τ M₁ = refl
subst-subst σ τ `zero = refl
subst-subst σ τ (`suc M) = cong `suc_ (subst-subst σ τ M)
subst-subst σ τ (recnat M M₁ M₂)
  rewrite subst-subst σ τ M | subst-subst σ τ M₁ | subst-subst σ τ M₂ = refl

subst-id : ∀ (M : Γ ⊢ A) → subst `_ M ≡ M
subst-id (` x) = refl
subst-id (ƛ M) = cong ƛ_ (trans (subst-cong (λ{ Z → refl ; (S x) → refl }) M) (subst-id M))
subst-id (M · M₁) rewrite subst-id M | subst-id M₁ = refl
subst-id `zero = refl
subst-id (`suc M) = cong `suc_ (subst-id M)
subst-id (recnat M M₁ M₂)
  rewrite subst-id M | subst-id M₁ | subst-id M₂ = refl

-- Extending a substitution by a term (mirrors extc for environments)

infixl 5 _,ₛ_

_,ₛ_ : Sub Γ Δ → Δ ⊢ A → Sub (Γ , A) Δ
(σ ,ₛ M) Z     = M
(σ ,ₛ M) (S x) = σ x

exts-,ₛ : ∀ (σ : Sub Γ Δ) (W : Δ ⊢ B) (N : Γ , B ⊢ A)
  → subst (exts σ) N [ W ] ≡ subst (σ ,ₛ W) N
exts-,ₛ σ W N = trans (subst-subst (exts σ) (σ₀ W) N)
                      (subst-cong (λ{ Z → refl
                                    ; (S x) → trans (subst-rename S_ (σ₀ W) (σ x))
                                                    (subst-id (σ x)) }) N)

-- The Logical Relation

-- 𝕍⟦ A ⟧ v V:  the closed syntactic value V represents the semantic value v.
-- 𝔼⟦ A ⟧ v M:  the closed term M reduces to a value representing v.
--

𝕍⟦_⟧ : ∀ (A : Type) → 𝓣⟦ A ⟧ → ∅ ⊢ A → Set
𝔼⟦_⟧ : ∀ (A : Type) → 𝓣⟦ A ⟧ → ∅ ⊢ A → Set

𝕍⟦ A ⇒ B ⟧ f V = Value V × (∀ {a : 𝓣⟦ A ⟧} {W : ∅ ⊢ A} → 𝕍⟦ A ⟧ a W → 𝔼⟦ B ⟧ (f a) (V · W))
𝕍⟦ `ℕ ⟧    n V = V ≡ numeral n

𝔼⟦ B ⟧ v M = ∃[ V ] ((M ⟶* V) × 𝕍⟦ B ⟧ v V)

𝕍-Value : ∀ {A} {v : 𝓣⟦ A ⟧} {V : ∅ ⊢ A} → 𝕍⟦ A ⟧ v V → Value V
𝕍-Value {A ⇒ B}     𝕍v  = proj₁ 𝕍v
𝕍-Value {`ℕ}    {n} refl = numeral-Value n

-- 𝔾⟦ Γ ⟧ γ σ:  the closing substitution σ is pointwise related to the
-- semantic environment γ.

𝔾⟦_⟧ : ∀ (Γ : Context) → 𝓒⟦ Γ ⟧ → Sub Γ ∅ → Set
𝔾⟦ Γ ⟧ γ σ = ∀ {A} (x : Γ ∋ A) →  𝕍⟦ A ⟧ (γ A x) (σ x)

𝔾-ext : ∀ {γ : 𝓒⟦ Γ ⟧} {σ : Sub Γ ∅} {a : 𝓣⟦ A ⟧} {W : ∅ ⊢ A}
  → 𝔾⟦ Γ ⟧ γ σ
  → 𝕍⟦ A ⟧ a W
  → 𝔾⟦ Γ , A ⟧ (extc γ a) (σ ,ₛ W)
𝔾-ext 𝔾γσ 𝕍aW Z     = 𝕍aW
𝔾-ext 𝔾γσ 𝕍aW (S x) = 𝔾γσ x

-- Recursion on a numeral mirrors recnat′ on the semantic side.

𝔼-recnat : ∀ (n : ℕ) {m₁ : 𝓣⟦ A ⟧} {m₂ : 𝓣⟦ `ℕ ⇒ A ⇒ A ⟧} {M₁ : ∅ ⊢ A} {M₂ : ∅ ⊢ `ℕ ⇒ A ⇒ A}
  → M₁ ∈ 𝔼⟦ A ⟧ m₁
  → M₂ ∈ 𝔼⟦ `ℕ ⇒ A ⇒ A ⟧ m₂
  → (recnat (numeral n) M₁ M₂) ∈ 𝔼⟦ A ⟧ (recnat′ n m₁ m₂)
𝔼-recnat zero ⟨ V , ⟨ M₁⟶*V , 𝕍v ⟩ ⟩ 𝔼₂ = ⟨ V , ⟨ β-zero ∷ M₁⟶*V , 𝕍v ⟩ ⟩
𝔼-recnat (suc n) 𝔼₁ 𝔼₂ with 𝔼₂ | 𝔼-recnat n 𝔼₁ 𝔼₂
... | ⟨ N₂ , ⟨ M₂⟶*N₂ , 𝕍N₂ ⟩ ⟩ | ⟨ Vᵣ , ⟨ R⟶*Vᵣ , 𝕍Vᵣ ⟩ ⟩
  with proj₂ 𝕍N₂ {n} {numeral n} refl
... | ⟨ F , ⟨ N₂·n⟶*F , 𝕍F ⟩ ⟩ with proj₂ 𝕍F 𝕍Vᵣ
... | ⟨ V , ⟨ F·Vᵣ⟶*V , 𝕍V ⟩ ⟩ =
  ⟨ V , ⟨ β-suc (numeral-Value n)
          ∷ (ξ*-·₁ (ξ*-·₁ M₂⟶*N₂)
          ++ ξ*-·₁ N₂·n⟶*F
          ++ ξ*-·₂ (proj₁ 𝕍F) R⟶*Vᵣ
          ++ F·Vᵣ⟶*V) , 𝕍V ⟩ ⟩

-- The Fundamental Lemma

-- Every well-typed term, closed by a substitution related to the environment,
-- reduces to a value representing its denotation.

fundamental : ∀ (M : Γ ⊢ A) {γ : 𝓒⟦ Γ ⟧} {σ : Sub Γ ∅}
  → 𝔾⟦ Γ ⟧ γ σ
  → 𝔼⟦ A ⟧ (𝓔⟦ M ⟧ γ) (subst σ M)


fundamental (` x) {γ} {σ} 𝔾γσ = ⟨ σ x , ⟨ ∎ , 𝔾γσ x ⟩ ⟩
fundamental {A = A ⇒ B} (ƛ N) {γ} {σ} 𝔾γσ =
  ⟨ ƛ subst (exts σ) N , ⟨ ∎ , ⟨ ƛ subst (exts σ) N , claim ⟩ ⟩ ⟩
  where
  claim : ∀ {a : 𝓣⟦ A ⟧} {W : ∅ ⊢ A}
    → 𝕍⟦ A ⟧ a W
    → 𝔼⟦ B ⟧ (𝓔⟦ N ⟧ (extc γ a)) ((ƛ subst (exts σ) N) · W)
  claim {a} {W} 𝕍aW with fundamental N (𝔾-ext 𝔾γσ 𝕍aW)
  ... | ⟨ V , ⟨ N′⟶*V , 𝕍v ⟩ ⟩ =
    ⟨ V , ⟨ β-ƛ (𝕍-Value 𝕍aW) ∷ ≡-subst (_⟶* V) (sym (exts-,ₛ σ W N)) N′⟶*V , 𝕍v ⟩ ⟩
fundamental (M · M₁) 𝔾γσ with fundamental M 𝔾γσ | fundamental M₁ 𝔾γσ
... | ⟨ L , ⟨ σM⟶*L , 𝕍f ⟩ ⟩ | ⟨ W , ⟨ σM₁⟶*W , 𝕍a ⟩ ⟩ with proj₂ 𝕍f 𝕍a
... | ⟨ V , ⟨ L·W⟶*V , 𝕍v ⟩ ⟩ =
  ⟨ V , ⟨ ξ*-·₁ σM⟶*L ++ ξ*-·₂ (proj₁ 𝕍f) σM₁⟶*W ++ L·W⟶*V , 𝕍v ⟩ ⟩
fundamental `zero 𝔾γσ = ⟨ `zero , ⟨ ∎ , refl ⟩ ⟩
fundamental (`suc M) 𝔾γσ with fundamental M 𝔾γσ
... | ⟨ V , ⟨ σM⟶*V , V≡ ⟩ ⟩ = ⟨ `suc V , ⟨ ξ*-suc σM⟶*V , cong `suc_ V≡ ⟩ ⟩
fundamental (recnat M M₁ M₂) {γ} {σ} 𝔾γσ with fundamental M 𝔾γσ
... | ⟨ V , ⟨ σM⟶*V , refl ⟩ ⟩
  with 𝔼-recnat (𝓔⟦ M ⟧ γ) (fundamental M₁ 𝔾γσ) (fundamental M₂ 𝔾γσ)
... | ⟨ V′ , ⟨ R⟶*V′ , 𝕍v ⟩ ⟩ = ⟨ V′ , ⟨ ξ*-recnat σM⟶*V ++ R⟶*V′ , 𝕍v ⟩ ⟩

-- Completeness Theorems

-- Closed terms need no environment and are closed by the identity substitution.

γ∅ : 𝓒⟦ ∅ ⟧
γ∅ A ()

𝔾∅ : 𝔾⟦ ∅ ⟧ γ∅ `_
𝔾∅ ()

-- Every closed term reduces to a value representing its denotation.

completeness : ∀ (M : ∅ ⊢ A) → ∃[ V ] ((M ⟶* V) × 𝕍⟦ A ⟧ (𝓔⟦ M ⟧ γ∅) V)
completeness M with fundamental M 𝔾∅
... | ⟨ V , ⟨ σM⟶*V , 𝕍v ⟩ ⟩ = ⟨ V , ⟨ ≡-subst (_⟶* V) (subst-id M) σM⟶*V , 𝕍v ⟩ ⟩

-- In particular, a closed term of type `ℕ reduces to the numeral computed by
-- the denotational semantics ...

completeness-ℕ : ∀ (M : ∅ ⊢ `ℕ) → M ⟶* numeral (𝓔⟦ M ⟧ γ∅)
completeness-ℕ M with completeness M
... | ⟨ V , ⟨ M⟶*V , refl ⟩ ⟩ = M⟶*V

-- ... and hence closed terms of type `ℕ with the same denotation reduce to a
-- common term.  Together with soundness, the denotational semantics equates
-- exactly the closed `ℕ-terms that reduce to the same numeral.

complete : ∀ (M N : ∅ ⊢ `ℕ)
  → 𝓔⟦ M ⟧ γ∅ ≡ 𝓔⟦ N ⟧ γ∅
  → ∃[ V ] ((M ⟶* V) × (N ⟶* V))
complete M N 𝓔M≡𝓔N =
  ⟨ numeral (𝓔⟦ N ⟧ γ∅)
  , ⟨ ≡-subst (λ n → M ⟶* numeral n) 𝓔M≡𝓔N (completeness-ℕ M)
    , completeness-ℕ N ⟩ ⟩

-- just termination

𝔙⟦_⟧ : ∀ A → ∅ ⊢ A → Set
𝔈⟦_⟧ : ∀ A → ∅ ⊢ A → Set

𝔙⟦ A ⇒ B ⟧ V = ∃[ L′ ] (V ≡ ƛ L′) × (∀ W → W ∈ 𝔙⟦ A ⟧ → L′ [ W ] ∈ 𝔈⟦ B ⟧)
𝔙⟦ `ℕ ⟧ V = ∃[ n ] V ≡ numeral n

𝔈⟦ B ⟧ M = ∃[ V ] ((M ⟶* V) × V ∈ 𝔙⟦ B ⟧)

𝔙-Value : ∀ {A} {V : ∅ ⊢ A} → V ∈ 𝔙⟦ A ⟧ → Value V
𝔙-Value {A ⇒ B} ⟨ L′ , ⟨ refl , _ ⟩ ⟩ = ƛ L′
𝔙-Value {`ℕ} ⟨ n , refl ⟩ = numeral-Value n

𝔊⟦_⟧ : ∀ (Γ : Context) → Sub Γ ∅ → Set
𝔊⟦ Γ ⟧ σ = ∀ {A} x → σ x ∈ 𝔙⟦ A ⟧

𝔊-ext : ∀ {σ : Sub Γ ∅} {W : ∅ ⊢ A}
  → 𝔊⟦ Γ ⟧ σ
  → 𝔙⟦ A ⟧ W
  → 𝔊⟦ Γ , A ⟧ (σ ,ₛ W)
𝔊-ext 𝔊 𝔙 Z = 𝔙
𝔊-ext 𝔊 𝔙 (S x) = 𝔊 x

_⊨_ : ∀ {A} → (Γ : Context) → (M : Γ ⊢ A) → Set
_⊨_ {A} Γ M = ∀ σ → σ ∈ 𝔊⟦ Γ ⟧ → subst σ M ∈ 𝔈⟦ A ⟧

σ∅ : Sub ∅ ∅
σ∅ ()

𝔊∅ : 𝔊⟦ ∅ ⟧ σ∅
𝔊∅ ()

-- context lemma for recnat

ft-recnat : ∀ n → {M : Γ ⊢ A} {N : Γ ⊢ `ℕ ⇒ A ⇒ A} → Γ ⊨ M → Γ ⊨ N → Γ ⊨ recnat (numeral n) M N
ft-recnat zero ⊨M ⊨N σ σ∈
  with ⊨M σ σ∈
... | ⟨ W , ⟨ σM⟶*W , W∈𝔙 ⟩ ⟩ = ⟨ W , ⟨ (β-zero ∷ σM⟶*W) , W∈𝔙 ⟩ ⟩
ft-recnat (suc n) {M}{N} ⊨M ⊨N σ σ∈
  with ⊨N σ σ∈
... | ⟨ W , ⟨ σN⟶*W , ⟨ L′ , ⟨ refl , ass₁ ⟩ ⟩ ⟩ ⟩
  with ass₁ (numeral n) ⟨ n , refl ⟩
... | ⟨ A⇒A , ⟨ L′[n]⟶*WA , ⟨ L″ , ⟨ refl , ass₂ ⟩ ⟩ ⟩ ⟩
  with ft-recnat n {M}{N} ⊨M ⊨N σ σ∈
... | ⟨ WA , ⟨ XX⟶*WA , WA∈𝔙 ⟩ ⟩
  with ass₂ WA WA∈𝔙
... | ⟨ V , ⟨ L″[WA]⟶*V , V∈𝔙 ⟩ ⟩
  rewrite sym (numeral-subst {n = n}{σ}) =
    ⟨ V , ⟨ β-suc (numeral-Value n) ∷
            (ξ*-·₁ (ξ*-·₁ σN⟶*W) ++
            (ξ-·₁ (β-ƛ (numeral-Value n)) ∷
            (ξ*-·₁ L′[n]⟶*WA) ++
            ξ*-·₂ (ƛ L″) XX⟶*WA ++
            (β-ƛ (𝔙-Value WA∈𝔙)) ∷
            L″[WA]⟶*V)) , V∈𝔙 ⟩ ⟩

-- fundamental theorem

ftlr : (M : Γ ⊢ A) → Γ ⊨ M
ftlr (` x) σ σ∈ = ⟨ σ x , ⟨ ∎ , σ∈ x ⟩ ⟩
ftlr (ƛ L) σ σ∈ = ⟨ ƛ (subst (exts σ) L)
                , ⟨ ∎ , ⟨ _ , ⟨ refl , (λ W W∈𝔙 → ≡-subst (_∈ 𝔈⟦ _ ⟧) (sym (exts-,ₛ σ W L)) (ftlr L (σ ,ₛ W) (𝔊-ext σ∈ W∈𝔙)) ) ⟩ ⟩ ⟩ ⟩
ftlr (_·_ {_}{A}{B} M N) σ σ∈
  with ftlr M σ σ∈
... | ⟨ ƛ L′ , ⟨ σM⟶*VM , ⟨ _ , ⟨ refl , ass ⟩ ⟩ ⟩ ⟩
  with ftlr N σ σ∈
... | ⟨ VN , ⟨ σN⟶*VN , VN∈𝔙 ⟩ ⟩
  with ass VN VN∈𝔙
... | ⟨ V , ⟨ L′[NV]⟶*V , V∈𝔙 ⟩ ⟩
    = ⟨ V , ⟨ (ξ*-·₁ σM⟶*VM ++ ξ*-·₂ (ƛ L′) σN⟶*VN ++ β-ƛ (𝔙-Value VN∈𝔙) ∷ L′[NV]⟶*V) , V∈𝔙 ⟩ ⟩
ftlr `zero σ σ∈ = ⟨ numeral zero , ⟨ ∎ , ⟨ zero , refl ⟩ ⟩ ⟩
ftlr (`suc M) σ σ∈
  with ftlr M σ σ∈
... | ⟨ W , ⟨ σM⟶*W , ⟨ n , refl ⟩ ⟩ ⟩ = ⟨ `suc W , ⟨ ξ*-suc σM⟶*W , ⟨ suc n , refl ⟩ ⟩ ⟩
ftlr (recnat L M N) σ σ∈
  with ftlr L σ σ∈
... | ⟨ Vn , ⟨ σL⟶*Vn , ⟨ n , refl ⟩ ⟩ ⟩
  with ft-recnat n {M = M}{N = N} (ftlr M) (ftlr N) σ σ∈
... | ⟨ V , ⟨ rec-num⟶*V , V∈𝔙 ⟩ ⟩
  rewrite sym (numeral-subst {n = n}{σ}) = ⟨ V , ⟨ ((ξ*-recnat σL⟶*Vn) ++ rec-num⟶*V) , V∈𝔙 ⟩ ⟩
