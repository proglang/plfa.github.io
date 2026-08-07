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
  ... | cv = interpret (extend γ′ cv) {!L′!} {-1-}
  interpret γ `zero = `zero
  interpret γ (`suc M) = `suc (interpret γ M)
  interpret γ (case L M N)
    with interpret γ L
  ... | `zero = interpret γ M
  ... | `suc cv = interpret (extend γ cv) N
  interpret γ (μ M) = interpret γ {!M [ μ M ]!} {-2-}
\end{code}

The holes in the above interpreter are intentional.
If we fill the holes, the definition is no longer terminating.

At {-1-} we wish to invoke the interpreter recursively on an environment 
unrelated to γ and on a term L′ that is neither a subterm of L nor of M.
Consequently, Agda's termination checker refuses this call.

At {-2-} we wish to invoke the interpreter on a term that is strictly
larger than M. Again, this call is rejected by the termination checker.

But we can add gas and rewrite the interpreter to decrease the gas
at every step! Here is a working design for such a step-indexed interpreter.

\begin{code}
  interpret′ : ∀ {Γ}{A} → CEnv Γ → Γ ⊢ A → (ℕ → Maybe (CVal A))
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
\end{code}

Completeness of interpretation wrt the big-step semantics is easier to state and prove.

\begin{code}
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

For soundness, we first need to see that interpretation results are preserved
when increasing gas.

\begin{code}
  interpret′-mono : ∀ {Γ}{A} → (γ : CEnv Γ) (M : Γ ⊢ A)
    → ∀ {cv n m}
    → n ≤ m
    → interpret′ γ M n ≡ just cv
    → interpret′ γ M m ≡ just cv
  interpret′-mono γ M {n = zero} le ()
  interpret′-mono γ M {n = suc n} {m = zero} () eq
  interpret′-mono γ (` x) (s≤s le) refl = refl
  interpret′-mono γ (ƛ M) (s≤s le) refl = refl
  interpret′-mono γ (L · M) {cv} {suc n} {suc m} (s≤s le) eq
    with interpret′ γ L n in L-eq
  interpret′-mono γ (L · M) {cv} {suc n} {suc m} (s≤s le) () | nothing
  interpret′-mono γ (L · M) {cv} {suc n} {suc m} (s≤s le) eq | just (`clos γ′ L′)
    with interpret′ γ M n in M-eq
  interpret′-mono γ (L · M) {cv} {suc n} {suc m} (s≤s le) () | just (`clos γ′ L′) | nothing
  interpret′-mono γ (L · M) {cv} {suc n} {suc m} (s≤s le) eq | just (`clos γ′ L′) | just cv′
    rewrite interpret′-mono γ L le L-eq
          | interpret′-mono γ M le M-eq
    = interpret′-mono (extend γ′ cv′) L′ le eq
  interpret′-mono γ `zero (s≤s le) refl = refl
  interpret′-mono γ (`suc M) {cv} {suc n} {suc m} (s≤s le) eq
    with interpret′ γ M n in M-eq
  interpret′-mono γ (`suc M) {cv} {suc n} {suc m} (s≤s le) () | nothing
  interpret′-mono γ (`suc M) {cv} {suc n} {suc m} (s≤s le) refl | just cv′
    rewrite interpret′-mono γ M le M-eq
    = refl
  interpret′-mono γ (case L M N) {cv} {suc n} {suc m} (s≤s le) eq
    with interpret′ γ L n in L-eq
  interpret′-mono γ (case L M N) {cv} {suc n} {suc m} (s≤s le) () | nothing
  interpret′-mono γ (case L M N) {cv} {suc n} {suc m} (s≤s le) eq | just `zero
    rewrite interpret′-mono γ L le L-eq
    = interpret′-mono γ M le eq
  interpret′-mono γ (case L M N) {cv} {suc n} {suc m} (s≤s le) eq | just (`suc cv′)
    rewrite interpret′-mono γ L le L-eq
    = interpret′-mono (extend γ cv′) N le eq
  interpret′-mono γ (μ M) {cv} {suc n} {suc m} (s≤s le) eq =
    interpret′-mono γ (M [ μ M ]) le eq
\end{code}

With this monotonicity result, we can prove soundness.

\begin{code}
  sound : ∀ {Γ}{A} → (γ : CEnv Γ) (M : Γ ⊢ A) → (cv : CVal A)
    → γ ∥ M ⇓ cv
    → ∃[ n ] interpret′ γ M n ≡ just cv

  sound γ M cv ⇓-‵ = ⟨ 1 , refl ⟩
  sound γ M cv ⇓-ƛ = ⟨ 1 , refl ⟩
  sound γ (L · M) cv (⇓-· {γ′ = γ′}{L′ = L′}{V = v} L⇓clos M⇓v L′⇓cv)
    with sound γ L (`clos γ′ L′) L⇓clos
       | sound γ M v M⇓v
       | sound (extend γ′ v) L′ cv L′⇓cv
  ... | ⟨ nL , L-eq ⟩ | ⟨ nM , M-eq ⟩ | ⟨ nB , B-eq ⟩
    = ⟨ suc common , app-eq ⟩
      where
        common : ℕ
        common = nL ⊔ (nM ⊔ nB)

        app-eq : interpret′ γ (L · M) (suc common) ≡ just cv
        app-eq
          rewrite interpret′-mono γ L
                    (m≤m⊔n nL (nM ⊔ nB)) L-eq
                | interpret′-mono γ M
                    (≤-trans (m≤m⊔n nM nB) (m≤n⊔m nL (nM ⊔ nB))) M-eq
                | interpret′-mono (extend γ′ v) L′
                    (≤-trans (m≤n⊔m nM nB) (m≤n⊔m nL (nM ⊔ nB))) B-eq
          = refl
  sound γ M cv ⇓-zero = ⟨ 1 , refl ⟩
  sound γ (`suc M) (`suc cv) (⇓-suc M⇓cv)
    with sound γ M cv M⇓cv
  ... | ⟨ n , eq ⟩ = ⟨ suc n , suc-eq ⟩
    where
      suc-eq : interpret′ γ (`suc M) (suc n) ≡ just (`suc cv)
      suc-eq rewrite eq = refl
  sound γ (case L M N) cv (⇓-case-zero L⇓zero M⇓cv)
    with sound γ L `zero L⇓zero
       | sound γ M cv M⇓cv
  ... | ⟨ nL , L-eq ⟩ | ⟨ nM , M-eq ⟩
    = ⟨ suc common , case-zero-eq ⟩
      where
        common : ℕ
        common = nL ⊔ nM

        case-zero-eq : interpret′ γ (case L M N) (suc common) ≡ just cv
        case-zero-eq
          rewrite interpret′-mono γ L (m≤m⊔n nL nM) L-eq
                | interpret′-mono γ M (m≤n⊔m nL nM) M-eq
          = refl
  sound γ (case L M N) cv (⇓-case-suc {W = w} L⇓suc N⇓cv)
    with sound γ L (`suc w) L⇓suc
       | sound (extend γ w) N cv N⇓cv
  ... | ⟨ nL , L-eq ⟩ | ⟨ nN , N-eq ⟩
    = ⟨ suc common , case-suc-eq ⟩
      where
        common : ℕ
        common = nL ⊔ nN

        case-suc-eq : interpret′ γ (case L M N) (suc common) ≡ just cv
        case-suc-eq
          rewrite interpret′-mono γ L (m≤m⊔n nL nN) L-eq
                | interpret′-mono (extend γ w) N (m≤n⊔m nL nN) N-eq
          = refl
  sound γ (μ M) cv (⇓-μ M⇓cv)
    with sound γ (M [ μ M ]) cv M⇓cv
  ... | ⟨ n , eq ⟩ = ⟨ (suc n) , eq ⟩
\end{code}

