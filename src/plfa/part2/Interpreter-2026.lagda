---
title     : "Interpreter semantics"
permalink : /Interpreter/
---

\begin{code}
module plfa.part2.Interpreter-2026 where
\end{code}

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _<_; z<s; s<s; _≤_; z≤n; s≤s; _≤?_; _⊔_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m⊔n; m≤n⊔m)
open import Data.Maybe using (Maybe; nothing; just)
open import Relation.Nullary.Negation using (¬_)
open import Data.Product using (∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary.Decidable using (True; toWitness)

open import plfa.part2.DeBruijn-2026
open import plfa.part2.BigStep-2026

\end{code}

The naive approach to construct an interpreter does not work...

\begin{code}
module interpreter where

  interpret : ∀ {Γ}{A} → CEnv Γ → Γ ⊢ A → CVal A
  interpret γ (` x) = γ x
  interpret γ (ƛ M) = `clos γ M
  interpret γ (L · M)
    with interpret γ L
  ... | `clos γ′ L′
    with interpret γ M
  ... | cv = interpret (extend γ′ cv) {!L′!}
  interpret γ `zero = `zero
  interpret γ (`suc M) = `suc (interpret γ M)
  interpret γ (case L M N)
    with interpret γ L
  ... | `zero = interpret γ M
  ... | `suc cv = interpret (extend γ cv) N
  interpret γ (μ M) = interpret γ {!M [ μ M ]!} 
\end{code}

But we can add gas!

\begin{code}
  interpret′ : ∀ {Γ}{A} → CEnv Γ → Γ ⊢ A → ℕ → Maybe (CVal A)
  interpret′ γ _ zero = nothing
  interpret′ γ (` x) (suc _) = just (γ x)
  interpret′ γ (ƛ M) (suc _) = just (`clos γ M)
  interpret′ γ (L · M) (suc n)
    with interpret′ γ L n
  ... | nothing = nothing
  ... | just (`clos γ′ L′)
    with interpret′ γ M n
  ... | nothing = nothing
  ... | just cv = interpret′ (extend γ′ cv) L′ n
  interpret′ γ `zero (suc _) = just `zero
  interpret′ γ (`suc M) (suc n)
    with interpret′ γ M n
  ... | nothing = nothing
  ... | just cv = just (`suc cv)
  interpret′ γ (case L M N) (suc n)
    with interpret′ γ L n
  ... | nothing = nothing
  ... | just `zero = interpret′ γ M n
  ... | just (`suc cv) = interpret′ (extend γ cv) N n
  interpret′ γ (μ M) (suc n) = interpret′ γ (M [ μ M ]) n


  interpret′-mono : ∀ {Γ}{A} → (M : Γ ⊢ A) (γ : CEnv Γ)
    → ∀ {cv n m}
    → n ≤ m
    → interpret′ γ M n ≡ just cv
    → interpret′ γ M m ≡ just cv
  interpret′-mono M γ {n = zero} le ()
  interpret′-mono M γ {n = suc n} {m = zero} () eq
  interpret′-mono (` x) γ (s≤s le) refl = refl
  interpret′-mono (ƛ M) γ (s≤s le) refl = refl
  interpret′-mono (L · M) γ {cv} {suc n} {suc m} (s≤s le) eq
    with interpret′ γ L n in L-eq
  interpret′-mono (L · M) γ {cv} {suc n} {suc m} (s≤s le) () | nothing
  interpret′-mono (L · M) γ {cv} {suc n} {suc m} (s≤s le) eq | just (`clos γ′ L′)
    with interpret′ γ M n in M-eq
  interpret′-mono (L · M) γ {cv} {suc n} {suc m} (s≤s le) () | just (`clos γ′ L′) | nothing
  interpret′-mono (L · M) γ {cv} {suc n} {suc m} (s≤s le) eq | just (`clos γ′ L′) | just cv′
    rewrite interpret′-mono L γ le L-eq
          | interpret′-mono M γ le M-eq
    = interpret′-mono L′ (extend γ′ cv′) le eq
  interpret′-mono `zero γ (s≤s le) refl = refl
  interpret′-mono (`suc M) γ {cv} {suc n} {suc m} (s≤s le) eq
    with interpret′ γ M n in M-eq
  interpret′-mono (`suc M) γ {cv} {suc n} {suc m} (s≤s le) () | nothing
  interpret′-mono (`suc M) γ {cv} {suc n} {suc m} (s≤s le) refl | just cv′
    rewrite interpret′-mono M γ le M-eq
    = refl
  interpret′-mono (case L M N) γ {cv} {suc n} {suc m} (s≤s le) eq
    with interpret′ γ L n in L-eq
  interpret′-mono (case L M N) γ {cv} {suc n} {suc m} (s≤s le) () | nothing
  interpret′-mono (case L M N) γ {cv} {suc n} {suc m} (s≤s le) eq | just `zero
    rewrite interpret′-mono L γ le L-eq
    = interpret′-mono M γ le eq
  interpret′-mono (case L M N) γ {cv} {suc n} {suc m} (s≤s le) eq | just (`suc cv′)
    rewrite interpret′-mono L γ le L-eq
    = interpret′-mono N (extend γ cv′) le eq
  interpret′-mono (μ M) γ {cv} {suc n} {suc m} (s≤s le) eq =
    interpret′-mono (M [ μ M ]) γ le eq
\end{code}

Soundness and completeness of the interpreter wrt the big-step semantics

\begin{code}
  sound : ∀ {Γ}{A} → (M : Γ ⊢ A) (γ : CEnv Γ) → (cv : CVal A)
    → γ ∥ M ⇓ cv
    → ∃[ n ] interpret′ γ M n ≡ just cv
  sound M γ cv ⇓-‵ = ⟨ 1 , refl ⟩
  sound M γ cv ⇓-ƛ = ⟨ 1 , refl ⟩
  sound (L · M) γ cv (⇓-· {γ′ = γ′}{L′ = L′}{V = v} L⇓clos M⇓v L′⇓cv)
    with sound L γ (`clos γ′ L′) L⇓clos
       | sound M γ v M⇓v
       | sound L′ (extend γ′ v) cv L′⇓cv
  ... | ⟨ nL , L-eq ⟩ | ⟨ nM , M-eq ⟩ | ⟨ nB , B-eq ⟩
    = ⟨ suc common , app-eq ⟩
      where
        common : ℕ
        common = nL ⊔ (nM ⊔ nB)

        app-eq : interpret′ γ (L · M) (suc common) ≡ just cv
        app-eq
          rewrite interpret′-mono L γ
                    (m≤m⊔n nL (nM ⊔ nB)) L-eq
                | interpret′-mono M γ
                    (≤-trans (m≤m⊔n nM nB) (m≤n⊔m nL (nM ⊔ nB))) M-eq
                | interpret′-mono L′ (extend γ′ v)
                    (≤-trans (m≤n⊔m nM nB) (m≤n⊔m nL (nM ⊔ nB))) B-eq
          = refl
  sound M γ cv ⇓-zero = ⟨ 1 , refl ⟩
  sound (`suc M) γ (`suc cv) (⇓-suc M⇓cv)
    with sound M γ cv M⇓cv
  ... | ⟨ n , eq ⟩ = ⟨ suc n , suc-eq ⟩
    where
      suc-eq : interpret′ γ (`suc M) (suc n) ≡ just (`suc cv)
      suc-eq rewrite eq = refl
  sound (case L M N) γ cv (⇓-case-zero L⇓zero M⇓cv)
    with sound L γ `zero L⇓zero
       | sound M γ cv M⇓cv
  ... | ⟨ nL , L-eq ⟩ | ⟨ nM , M-eq ⟩
    = ⟨ suc common , case-zero-eq ⟩
      where
        common : ℕ
        common = nL ⊔ nM

        case-zero-eq : interpret′ γ (case L M N) (suc common) ≡ just cv
        case-zero-eq
          rewrite interpret′-mono L γ (m≤m⊔n nL nM) L-eq
                | interpret′-mono M γ (m≤n⊔m nL nM) M-eq
          = refl
  sound (case L M N) γ cv (⇓-case-suc {W = w} L⇓suc N⇓cv)
    with sound L γ (`suc w) L⇓suc
       | sound N (extend γ w) cv N⇓cv
  ... | ⟨ nL , L-eq ⟩ | ⟨ nN , N-eq ⟩
    = ⟨ suc common , case-suc-eq ⟩
      where
        common : ℕ
        common = nL ⊔ nN

        case-suc-eq : interpret′ γ (case L M N) (suc common) ≡ just cv
        case-suc-eq
          rewrite interpret′-mono L γ (m≤m⊔n nL nN) L-eq
                | interpret′-mono N (extend γ w) (m≤n⊔m nL nN) N-eq
          = refl
  sound (μ M) γ cv (⇓-μ M⇓cv)
    with sound (M [ μ M ]) γ cv M⇓cv
  ... | ⟨ n , eq ⟩ = ⟨ (suc n) , eq ⟩

  complete : ∀ {Γ}{A} → (γ : CEnv Γ) (M : Γ ⊢ A) → (cv : CVal A)
    → ∀ n → interpret′ γ M n ≡ just cv
    → γ ∥ M ⇓ cv

  complete γ M cv zero () 
  complete γ (` x) cv (suc n) refl = ⇓-‵
  complete γ (ƛ M) cv (suc n) refl = ⇓-ƛ
  complete γ (L · M) cv (suc n) int≡
    with interpret′ γ L n in L-eq
  ... | just f@(`clos γ′ L′)
    with interpret′ γ M n in M-eq
  ... | just x = ⇓-· (complete γ L f n L-eq)
                     (complete γ M x n M-eq)
                     (complete (extend γ′ x) L′ cv n int≡)
  complete γ `zero cv (suc n) refl = ⇓-zero
  complete γ (`suc M) cv (suc n) int≡
    with interpret′ γ M n in eq
  complete γ (`suc M) cv (suc n) refl | just x
    = ⇓-suc (complete γ M x n eq)
  complete γ (case L M N) cv (suc n) int≡
    with interpret′ γ L n in eq
  ... | just `zero = ⇓-case-zero (complete γ L `zero n eq)
                                 (complete γ M cv n int≡)
  ... | just (`suc x) = ⇓-case-suc (complete γ L (`suc x) n eq)
                                   (complete (extend γ x) N cv n int≡)
  complete γ (μ M) cv (suc n) int≡ = ⇓-μ (complete γ (M [ μ M ]) cv n int≡)
\end{code}
