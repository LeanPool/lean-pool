/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.RingTheory.Algebraic.Defs

/-!
# Basic definitions: logarithms of algebraic numbers and the space `LTilde`

* `StrongSix.logAlg` : the set `𝓛 = {ℓ ∈ ℂ | exp ℓ is algebraic}` of logarithms of (nonzero)
  algebraic numbers. It is a `ℚ`-vector subspace of `ℂ` (proved later).
* `StrongSix.LTilde` : the `Qbar`-vector space `LTilde` spanned by `1` and `𝓛`, i.e. the numbers
  `β₀ + β₁ ℓ₁ + ⋯ + βₙ ℓₙ` with `βᵢ` algebraic and `ℓᵢ ∈ 𝓛`.

Main statements (proved in later files):
* `StrongSix.StrongSixExponentials` (Roy 1992), with `Qbar`-linear independence hypotheses.
-/

@[expose] public section

namespace LeanPool

open Complex

namespace StrongSix

/-- `𝓛`: the complex logarithms of nonzero algebraic numbers. -/
def logAlg : Set ℂ := {ℓ | IsAlgebraic ℚ (exp ℓ)}

/-- `LTilde`: the `Qbar`-span of `1` and `𝓛`, i.e. numbers `β₀ + Σᵢ βᵢ ℓᵢ` with algebraic `βᵢ` and
`ℓᵢ ∈ 𝓛`. -/
def LTilde : Set ℂ :=
  {z | ∃ (n : ℕ) (β : Fin (n + 1) → ℂ) (ℓ : Fin n → ℂ),
      (∀ i, IsAlgebraic ℚ (β i)) ∧ (∀ i, ℓ i ∈ logAlg) ∧
      z = β 0 + ∑ i, β i.succ * ℓ i}

/-- Linear independence over the field `Qbar` of algebraic numbers (inside `ℂ`). -/
def QbarIndep {n : ℕ} (v : Fin n → ℂ) : Prop :=
  ∀ c : Fin n → ℂ, (∀ i, IsAlgebraic ℚ (c i)) → ∑ i, c i * v i = 0 → ∀ i, c i = 0

/-- **Strong six exponentials theorem** (Roy 1992, Corollary 2). If `x₁, x₂` are linearly
independent over `Qbar` and `y₁, y₂, y₃` are linearly independent over `Qbar`, one of the six
numbers
`xᵢ yⱼ` is not in `LTilde`.

(Independence over `Qbar` is essential: `LTilde` is a `Qbar`-vector space, so `x = (1, √2)` and
`y = (log 2, log 3, log 5)` give six products in `LTilde`.) -/
def StrongSixExponentials : Prop :=
  ∀ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), QbarIndep x → QbarIndep y →
    ∃ i j, x i * y j ∉ LTilde

end StrongSix

end LeanPool
