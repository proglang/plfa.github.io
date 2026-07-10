---
title     : "BigStep: Big-step semantics"
permalink : /BigStep/
---

\begin{code}
module plfa.part2.BigStep-2026 where
\end{code}

# Introduction

The preceding chapter defines an intrinsically-typed lambda calculus
using de Bruijn indices.  It also gives a small-step operational
semantics, written `M —→ N`, where each step performs one local
computation.  In this chapter we introduce a second presentation of
evaluation.

A _big-step semantics_ relates a closed term directly to the value it
computes.  We write this relation as `M ⇓ V`: the term `M` evaluates
to the value `V`.  Compared with small-step reduction, big-step
evaluation hides the intermediate states and focuses on the final
answer.  This makes it a convenient specification of interpreters and
evaluators, while small-step reduction remains useful for reasoning
about individual computation steps.

# Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _<_; z<s; s<s; _≤_; z≤n; s≤s; _≤?_)
open import Relation.Nullary.Negation using (¬_)
open import Data.Product using (∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary.Decidable using (True; toWitness)

open import plfa.part2.DeBruijn-2026
\end{code}

# Big-step evaluation

The big-step relation is indexed by the type of the input and output
terms.  Since both terms are closed, the context is always `∅`.
The intended reading of `M ⇓ V` is that evaluation of `M` terminates
with the value `V`.

\begin{code}
data _⇓_ : ∀ {A} → ∅ ⊢ A → ∅ ⊢ A → Set where

  ⇓-ƛ : ∀ {A}{B}{M : ∅ , A ⊢ B}
    → (ƛ M) ⇓ (ƛ M)

  ⇓-· : ∀ {A}{B}{L : ∅ ⊢ A ⇒ B}{L′ : ∅ , A ⊢ B}{M V : ∅ ⊢ A}{W}
    → L ⇓ (ƛ L′)
    → M ⇓ V
    → (L′ [ V ]) ⇓ W
    → (L · M) ⇓ W

  ⇓-zero : `zero ⇓ `zero

  ⇓-suc : ∀ {M}{V}
    → M ⇓ V
    → (`suc M) ⇓ (`suc V)

  ⇓-case-zero : ∀ {A}{L}{M : ∅ ⊢ A}{N}{V}
    → L ⇓ `zero
    → M ⇓ V
    → case L M N ⇓ V

  ⇓-case-suc :  ∀ {A}{L}{M : ∅ ⊢ A}{N}{V}{W}
    → L ⇓ (`suc W)
    → (N [ W ]) ⇓ V
    → case L M N ⇓ V

  ⇓-μ : ∀ {A}{M : ∅ , A ⊢ A}{V}
    → (M [ μ M ]) ⇓ V
    → (μ M) ⇓ V
\end{code}

The rules mirror the constructs of the language.
Lambda abstractions and zero are already values.  To evaluate an
application, first evaluate the operator to a lambda abstraction,
then evaluate the argument, and finally evaluate the body after
substituting the argument value for the bound variable.  Successor and
case evaluate their natural-number subterms, and recursion unfolds one
step before continuing.

# Evaluation returns values

The result of big-step evaluation should not be an arbitrary term: it
should be a syntactic value.  The following lemma records that fact.
It proceeds by induction over the big-step derivation.

\begin{code}
⇓-returns-V : ∀ {A}{M V : ∅ ⊢ A} → M ⇓ V → Value V
⇓-returns-V ⇓-ƛ = V-ƛ
⇓-returns-V (⇓-· L⇓ƛL′ M⇓V L′[V]⇓W)
  with ⇓-returns-V L⇓ƛL′
... | V-ƛ
  with ⇓-returns-V M⇓V
... | ih-M = ⇓-returns-V L′[V]⇓W
⇓-returns-V ⇓-zero = V-zero
⇓-returns-V (⇓-suc M⇓V) = V-suc (⇓-returns-V M⇓V)
⇓-returns-V (⇓-case-zero L⇓zero M⇓V)
  with ⇓-returns-V L⇓zero
... | V-zero = ⇓-returns-V M⇓V
⇓-returns-V (⇓-case-suc L⇓sucW N[W]⇓V)
  with ⇓-returns-V L⇓sucW
... | V-suc ih =  ⇓-returns-V N[W]⇓V
⇓-returns-V (⇓-μ M⇓V) = ⇓-returns-V M⇓V
\end{code}

# Relating big-step and small-step semantics

We next connect the big-step relation to the small-step reduction
relation from the previous chapter.  The desired theorem has two
directions:

  * _soundness_: if `M ⇓ V`, then `M —↠ V`;
  * _completeness_: if `M —↠ V` and `V` is a value, then `M ⇓ V`.

Before proving these statements, we collect a few standard lemmas
about multi-step reduction.

## Lifting reductions through contexts

If a single-step reduction can be lifted through some term context
`F`, then a multi-step reduction can be lifted through the same
context.  We use this generic lemma for successor and case terms.

\begin{code}
ξ-lift : ∀ {A B} {M N : ∅ ⊢ A}{F : ∅ ⊢ A → ∅ ⊢ B}
  → (ξ : ∀ {M}{N} → M —→ N → F M  —→ F N)
  → M —↠ N
  → F M —↠ F N
ξ-lift {F = F} ξ (M ∎) = F M ∎
ξ-lift ξ (L —→⟨ L—→M ⟩ M—↠N) = _ —→⟨ ξ L—→M ⟩ ξ-lift ξ M—↠N

ξ-suc-lift : ∀ {M N : ∅ ⊢ `ℕ}
  → M —↠ N →  `suc M —↠ `suc N
ξ-suc-lift = ξ-lift ξ-suc

ξ-case-lift : ∀ {A} {L L′ : ∅ ⊢ `ℕ}{M : ∅ ⊢ A} {N}
  → L —↠ L′ →  case L M N —↠ case L′ M N
ξ-case-lift = ξ-lift ξ-case
\end{code}

## Transitivity

Multi-step reduction is transitive.  The proof is structurally the
same as append for lists: append the first reduction sequence to the
front of the second one.

\begin{code}
—↠-trans : ∀ {A}{L M N : ∅ ⊢ A} → L —↠ M → M —↠ N → L —↠ N
—↠-trans (M ∎) M—↠N = M—↠N
—↠-trans (L —→⟨ x ⟩ L—↠M) M—↠N = L —→⟨ x ⟩ —↠-trans L—↠M M—↠N
\end{code}

# Completeness

Completeness says that if small-step reduction reaches a value, then
big-step evaluation reaches the same value.  The proof is split in
two.  First, we show how to expand a big-step derivation backwards
across one small step.  Second, we repeat this argument along a
multi-step reduction sequence.

Before the one-step lemma, we record two simple facts about values.
The lemma `value-refl` says that a value cannot evaluate to a
different result: if `V` is already a value and `V ⇓ W`, then `V` and
`W` must be the same term.  The lemma `value-self` says the
converse operational fact: every syntactic value evaluates to itself.
Both are proved by induction on the structure of the value.

It is tempting to prove the one-step lemma in the forward direction,
from `M —→ N` and `M ⇓ V` to `N ⇓ V`.  The module `wrong-direction`
shows that this statement can indeed be proved.  However, it is not
the direction needed for completeness.  In the inductive case of a
multi-step reduction

    L —→ M —↠ V

the induction hypothesis gives `M ⇓ V`; to conclude `L ⇓ V`, the
one-step lemma must move _backwards_ over the first step `L —→ M`.
Thus the useful statement is:

    M —→ N  →  N ⇓ V  →  M ⇓ V

The proof of this backward `complete-step` lemma is by case analysis
on the small-step rule.  For congruence rules such as `ξ-·₁`,
`ξ-·₂`, `ξ-suc`, and `ξ-case`, the proof recursively expands the
big-step derivation for the reduced subterm and then rebuilds the
same outer big-step rule.  For β-rules, the proof constructs the
big-step derivation that corresponds to the redex.  The `β-ƛ` case
uses `value-self` to show that the lambda and its argument evaluate
to themselves, then reuses the assumed evaluation of the substituted
body.  The `β-zero` and `β-suc` cases rebuild the appropriate case
rule; in the successor case, `value-self` supplies the evaluation of
the successor argument.  The `β-μ` case simply folds the evaluation of
the unfolded body back into the big-step rule for recursion.

Completeness for many steps then follows directly.  If the reduction
sequence has no steps, the starting term is already the final value,
so `value-self` applies.  If the sequence begins with one step, the
induction hypothesis evaluates the reduct, and `complete-step` moves
that evaluation back across the first step.

\begin{code}
value-refl : ∀{A}{V W : ∅ ⊢ A} → Value V →  V ⇓ W → V ≡ W
value-refl V-ƛ ⇓-ƛ = refl
value-refl V-zero ⇓-zero = refl
value-refl (V-suc val-V) (⇓-suc V⇓W) = cong `suc_ (value-refl val-V V⇓W)

value-self : ∀{A}{V : ∅ ⊢ A} → Value V → V ⇓ V
value-self V-ƛ = ⇓-ƛ
value-self V-zero = ⇓-zero
value-self (V-suc val-V) = ⇓-suc (value-self val-V)

module wrong-direction where -- ;-)
  complete-step : ∀ {A} {M N V : ∅ ⊢ A}
    → M —→ N → M ⇓ V → N ⇓ V
  complete-step (ξ-·₁ M—→N) (⇓-· M⇓V M⇓V₁ M⇓V₂)
    with complete-step M—→N M⇓V
  ... | N⇓V = ⇓-· N⇓V M⇓V₁ M⇓V₂
  complete-step (ξ-·₂ val-V M—→N) (⇓-· M⇓V M⇓V₁ M⇓V₂)
    with value-refl val-V M⇓V
  ... | refl
    with complete-step M—→N M⇓V₁
  ... | N⇓V₁ = ⇓-· M⇓V N⇓V₁ M⇓V₂
  complete-step (β-ƛ val-W) (⇓-· ⇓-ƛ M⇓V₁ M⇓V₂)
    with value-refl val-W M⇓V₁
  ... | refl = M⇓V₂
  complete-step (ξ-suc M—→N) (⇓-suc M⇓V) = ⇓-suc (complete-step M—→N M⇓V)
  complete-step (ξ-case M—→N) (⇓-case-zero M⇓V M⇓V₁)
    with complete-step M—→N M⇓V
  ... | M′⇓V = ⇓-case-zero M′⇓V M⇓V₁
  complete-step (ξ-case M—→N) (⇓-case-suc M⇓V M⇓V₁)
    with complete-step M—→N M⇓V
  ... | M′⇓V = ⇓-case-suc M′⇓V M⇓V₁
  complete-step β-zero (⇓-case-zero ⇓-zero M⇓W) = M⇓W
  complete-step (β-suc val-V) (⇓-case-suc (⇓-suc M⇓V) M⇓W)
    with value-refl val-V M⇓V
  ... | refl = M⇓W
  complete-step β-μ (⇓-μ M⇓V) = M⇓V

complete-step : ∀ {A} {M N V : ∅ ⊢ A}
  → M —→ N → N ⇓ V → M ⇓ V
complete-step (ξ-·₁ M—→N) (⇓-· N⇓V N⇓V₁ N⇓V₂) = ⇓-· (complete-step M—→N N⇓V) N⇓V₁ N⇓V₂
complete-step (ξ-·₂ val-V M—→N) (⇓-· N⇓V N⇓V₁ N⇓V₂) = ⇓-· N⇓V (complete-step M—→N N⇓V₁) N⇓V₂
complete-step (β-ƛ val-W) N⇓V = ⇓-· (value-self V-ƛ) (value-self val-W) N⇓V
complete-step (ξ-suc M—→N) (⇓-suc N⇓V) = ⇓-suc (complete-step M—→N N⇓V)
complete-step (ξ-case M—→N) (⇓-case-zero N⇓V N⇓V₁) = ⇓-case-zero (complete-step M—→N N⇓V) N⇓V₁
complete-step (ξ-case M—→N) (⇓-case-suc N⇓V N⇓V₁) = ⇓-case-suc (complete-step M—→N N⇓V) N⇓V₁
complete-step β-zero N⇓V = ⇓-case-zero ⇓-zero N⇓V
complete-step (β-suc val-V) N⇓V = ⇓-case-suc (⇓-suc (value-self val-V)) N⇓V
complete-step β-μ N⇓V = ⇓-μ N⇓V


completeness : ∀ {A} {M V : ∅ ⊢ A}
  → M —↠ V → Value V → M ⇓ V
completeness (V ∎) val-V = value-self val-V
completeness (L —→⟨ L—→M ⟩ M—↠V) val-V
  with completeness M—↠V val-V
... | M⇓V = complete-step L—→M M⇓V 
\end{code}

# Soundness

Soundness goes in the other direction: every big-step derivation can
be expanded into a multi-step reduction from the input term to the
same value.  The proof follows the shape of the big-step derivation.
In the application case, the reductions for the operator and argument
are lifted into the corresponding evaluation contexts before the
β-rule is applied.

\begin{code}
soundness : ∀ {A} {M V : ∅ ⊢ A}
  → M ⇓ V → M —↠ V
soundness (⇓-ƛ {M = M}) = ƛ M ∎
soundness (⇓-· {L′ = L′}{M = M} L⇓ƛL′ M⇓V L′[V]⇓W)
  using red1 ← ξ-lift (ξ-·₁ {M = M}) (soundness L⇓ƛL′)
  using red2 ← ξ-lift (ξ-·₂ {V = ƛ L′} V-ƛ) (soundness M⇓V)
  using red3 ← —↠-trans red1 red2
  = —↠-trans red3 (_ —→⟨ β-ƛ (⇓-returns-V M⇓V) ⟩ soundness L′[V]⇓W)
soundness ⇓-zero = `zero ∎
soundness (⇓-suc M⇓V) = ξ-lift ξ-suc (soundness M⇓V)
soundness (⇓-case-zero {M = M}{N = N} L⇓zero M⇓V)
  using red ← ξ-case-lift{M = M}{N = N} (soundness L⇓zero)
    = —↠-trans red ((case `zero M N) —→⟨ β-zero ⟩ (soundness M⇓V))
soundness (⇓-case-suc {M = M}{N = N} L⇓suc N⇓V)
  using red ← ξ-case-lift{M = M}{N = N} (soundness L⇓suc)
  with ⇓-returns-V L⇓suc
... | V-suc val-W
  = —↠-trans red (case (`suc _) M N —→⟨ β-suc val-W ⟩ soundness N⇓V)
soundness (⇓-μ {M = M} M⇓V) = μ M —→⟨ β-μ ⟩ soundness M⇓V
\end{code}

The proof uses the big-step derivation as its induction structure.
Each constructor of `_⇓_` explains why the source term evaluates, and
the corresponding clause of `soundness` turns that explanation into a
small-step reduction sequence.

For values, no computation is required.  A lambda abstraction reduces
to itself by the empty multi-step sequence `ƛ M ∎`, and zero reduces
to itself by `` `zero ∎ ``.  The successor case is also direct: by the
induction hypothesis, `M` reduces to `V`; applying `ξ-suc` at every
step lifts this sequence to a reduction from `` `suc M `` to
`` `suc V ``.

The application case is the main one.  From the big-step derivation we
know three things: the operator `L` evaluates to a lambda `ƛ L′`, the
argument `M` evaluates to a value `V`, and the substituted body
`L′ [ V ]` evaluates to `W`.  The induction hypotheses give
multi-step reductions for each of these evaluations.  The first
reduction is lifted into the left side of the application with
`ξ-·₁`, producing a reduction from `L · M` to `(ƛ L′) · M`.  The
second reduction is lifted into the right side of the application
with `ξ-·₂`; this rule requires the operator to be a value, supplied
by `V-ƛ`.  After both subterms have been reduced, the β-rule
`β-ƛ` takes the single step from `(ƛ L′) · V` to `L′ [ V ]`.  Finally,
the induction hypothesis for the body evaluation reduces `L′ [ V ]`
to `W`.  The intermediate sequences are joined with `—↠-trans`.

The two case-expression clauses follow the same pattern.  First, the
scrutinee reduction is lifted into the `case` context.  If the
scrutinee evaluates to `zero`, the β-rule `β-zero` selects the zero
branch and the induction hypothesis for that branch finishes the
reduction.  If the scrutinee evaluates to `suc W`, the lemma
`⇓-returns-V` tells us that `W` is a value, which is exactly the
premise required by `β-suc`; after this step, the induction hypothesis
for the substituted successor branch completes the proof.

The recursion case is the smallest computational case.  The small-step
semantics unfolds `μ M` by one `β-μ` step to `M [ μ M ]`, and the
induction hypothesis then reduces that unfolded term to the value
produced by the big-step derivation.



# Big-step evaluation with environments

The first big-step relation uses substitution directly.  A more
implementation-oriented evaluator can instead carry an environment
that maps variables to closed terms.  The following definitions start
that development.

\begin{code}
Env : Context → Set
Env Γ = Sub Γ ∅
\end{code}

An environment is just a substitution from the current context to the
empty context.  Thus an entry for a variable is a closed term of the
appropriate type.  One might try to define an environment-based
big-step relation that still returns closed terms:

    data _∣_⇓_ : ∀ {Γ}{A} → Env Γ → Γ ⊢ A → ∅ ⊢ A → Set where

      ⇓-‵ : ∀ {Γ}{A} {σ : Env Γ}{x : Γ ∋ A}
        → σ ∣ ` x ⇓ σ x

      ⇓-ƛ : ∀ {Γ}{A}{B} {σ : Env Γ}{M : Γ , A ⊢ B}
        → σ ∣ (ƛ M) ⇓ ?

This is where the design breaks: the result type expects a closed
term, but evaluating a lambda in an environment should produce a
closure, not a substituted lambda term.

σ = []
(λy λx → y) 42
--->
σ = y ↦ 42
λ x → y


The lambda case exposes the limitation of this representation.  A
lambda term with free variables cannot be returned as a closed value
by itself; it must be paired with the environment that gives meanings
to those variables.  That pair is a _closure_, which is the next
structure needed for this development.

We therefore separate syntactic terms from the values produced by the
environment-based evaluator.  The type `CVal A` is the type of
semantic values of object-language type `A`.  Natural numbers are
represented by `zero` and `suc` values.  Function values are
represented by closures: a closure `` `clos γ M `` stores both a body
`M` and the environment `γ` in which that body was created.

The type `CEnv Γ` is the type of closure environments for context
`Γ`.  Such an environment maps every variable in `Γ` to a semantic
value of the corresponding type.  The definitions of `CVal` and
`CEnv` depend on each other: closures contain environments, and
environments return closure values.  This is why `CEnv` is declared
before `CVal` and defined afterwards.

When evaluation enters the body of a lambda abstraction, the current
environment must be extended with a value for the newly bound
variable.  The function `extend γ v` does exactly that.  The newest
variable `Z` is mapped to `v`, while an older variable `S x` is looked
up in the previous environment `γ`.

\begin{code}
CEnv : Context → Set

data CVal : Type → Set where
  `zero : CVal `ℕ
  `suc_ : CVal `ℕ → CVal `ℕ
  `clos : ∀ {Γ}{A}{B} → CEnv Γ → Γ , A ⊢ B → CVal (A ⇒ B)

CEnv Γ = ∀ {A} → Γ ∋ A → CVal A

extend : ∀ {Γ}{A} → CEnv Γ → CVal A → CEnv (Γ , A)
extend γ v Z = v
extend γ v (S x) = γ x
\end{code}

The environment-based big-step relation is written `γ ∥ M ⇓ V`.
It says that, under closure environment `γ`, the term `M` evaluates
directly to the semantic value `V`.  Unlike the earlier relation
`M ⇓ V`, the result is not a closed term but a member of `CVal`.
This lets lambda abstraction return a closure without first
substituting its free variables away.

\begin{code}
data _∥_⇓_ : ∀ {Γ}{A} → CEnv Γ → Γ ⊢ A → CVal A → Set where
  ⇓-‵ : ∀ {Γ}{A}{γ : CEnv Γ} {x : Γ ∋ A}
    → γ ∥ ` x ⇓ γ x

  ⇓-ƛ : ∀ {Γ}{A}{B} {γ : CEnv Γ}{M : Γ , A ⊢ B}
    → γ ∥ ƛ M ⇓ `clos γ M

  ⇓-· : ∀ {Γ}{A}{B}{γ : CEnv Γ}{L : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
          {Γ′}{γ′ : CEnv Γ′}{L′ : Γ′ , A ⊢ B}
          {V : CVal A}{W : CVal B}
    → γ ∥ L ⇓ `clos γ′ L′
    → γ ∥ M ⇓ V
    → extend γ′ V ∥ L′ ⇓ W
    → γ ∥ (L · M) ⇓ W

  ⇓-zero : ∀ {Γ}{γ : CEnv Γ}
    → γ ∥ `zero ⇓ `zero

  ⇓-suc :  ∀ {Γ}{γ : CEnv Γ}{M : Γ ⊢ `ℕ}{V : CVal `ℕ}
    → γ ∥ M ⇓ V
    → γ ∥ (`suc M) ⇓ (`suc V)

  ⇓-case-zero : ∀ {Γ}{γ : CEnv Γ}{A}{L}{M : Γ ⊢ A}{N}{V}
    → γ ∥ L ⇓ `zero
    → γ ∥ M ⇓ V
    → γ ∥ case L M N ⇓ V

  ⇓-case-suc :  ∀{Γ}{γ : CEnv Γ} {A}{L}{M : Γ ⊢ A}{N}{V}{W}
    → γ ∥ L ⇓ (`suc W)
    → extend γ W ∥ N ⇓ V
    → γ ∥ case L M N ⇓ V

  -- not cool to use substitution for recursion :,-(
  -- but μ M is not a value so we cannot extend γ with it
  ⇓-μ : ∀ {Γ}{γ : CEnv Γ} {A}{M : Γ , A ⊢ A}{V}
    → γ ∥ (M [ μ M ]) ⇓ V
    → γ ∥ (μ M) ⇓ V
\end{code}

The rules follow the structure of terms.

* A variable is evaluated by looking it up in the environment.

* A lambda abstraction evaluates to a closure containing the current
  environment and the lambda body.

* An application first evaluates the operator to a closure, then
  evaluates the argument to a value.  The body of the closure is then
  evaluated in the closure's saved environment, extended with the
  argument value.

* Zero evaluates to zero, and successor evaluates its subterm before
  rebuilding the successor value.

* A case expression evaluates its scrutinee first.  If the scrutinee
  is zero, the zero branch is evaluated in the current environment.
  If the scrutinee is a successor value, the successor branch is
  evaluated in an environment extended with the predecessor.

* The rule for recursion still uses substitution to unfold `μ M`.
  This is less satisfying than the other rules because it steps
  outside the closure-environment discipline, but it is enough for the
  examples below.

Example

\begin{code}
Ex2+2 : ∅ ⊢ `ℕ
Ex2+2 = plus · two · two

twoV : CVal `ℕ
twoV = `suc (`suc `zero)

fourV : CVal `ℕ
fourV = `suc (`suc twoV)

two⇓ : ∀ {Γ}{γ : CEnv Γ} → γ ∥ two ⇓ twoV
two⇓ = ⇓-suc (⇓-suc ⇓-zero)

_ : (λ ()) ∥ Ex2+2 ⇓ fourV
_ =
  ⇓-·
    (⇓-·
      (⇓-μ ⇓-ƛ)
      two⇓
      ⇓-ƛ)
    two⇓
    (⇓-case-suc
      ⇓-‵
      (⇓-suc
        (⇓-·
          (⇓-·
            (⇓-μ ⇓-ƛ)
            ⇓-‵
            ⇓-ƛ)
          ⇓-‵
          (⇓-case-suc
            ⇓-‵
            (⇓-suc
              (⇓-·
                (⇓-·
                  (⇓-μ ⇓-ƛ)
                  ⇓-‵
                  ⇓-ƛ)
                ⇓-‵
                (⇓-case-zero
                  ⇓-‵
                  ⇓-‵)))))))
\end{code}

Discussion about fixed point / recursion.

    plus : Term
    plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
             case ` "m"
               [zero⇒ ` "n"
               |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]

    plus′ = ƛ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
             case ` "m"
               [zero⇒ ` "n"
               |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]

    x is fixed point of F :  F(x) = x

    plus is fixed point of plus′:
    plus' (plus) =
      ƛ "m" ⇒ ƛ "n" ⇒
             case ` "m"
               [zero⇒ ` "n"
               |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ]
            = plus



% Local Variables:
% mode: agda2
% End:
