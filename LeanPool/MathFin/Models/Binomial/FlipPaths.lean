/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring.RingNF

/-!
# The pathwise language of the binomial tree

Coin-flip paths `ω : ℕ → Bool`, processes `X : ℕ → (ℕ → Bool) → ℝ`, and the **node average**
`q·X_{n+1}(…,↑) + (1 − q)·X_{n+1}(…,↓)` over the two children of a node, the explicit form of the
conditional expectation for the binomial filtration. This file is the measure-free layer:

* `PathAdaptedAt n X` — `X` depends only on the first `n` flips. It is the concrete face of
  Mathlib's `StronglyMeasurable[flipFiltration n]` (`stronglyMeasurable_flipFiltration_iff`,
  `Models/Binomial/PathMeasure.lean`), which is what theorems about martingales state.
* `hedgeRatio M S n ω` — the node-wise delta `ΔM_{n+1} / ΔS_{n+1}` across the two children, and
  `repr_one_step`, the one-period delta hedge: under the node-average condition for `M` and `S`,
  `M_{n+1} − M_n = hedgeRatio · (S_{n+1} − S_n)` on every path. The argument is purely algebraic.

The martingale representation theorem built from it, for Mathlib's `Martingale` of the flip
filtration, is `binomial_martingale_representation`
(`Models/Binomial/MartingaleRepresentation.lean`).

## Main definitions

* `PathAdaptedAt`: a function of a coin-flip path `ω : ℕ → Bool` is `n`-adapted when it depends
  only on the first `n` flips.
* `hedgeRatio`: the node-wise hedge ratio of `M` against `S`, the change in `M` over the change
  in `S` across the two children of a node.

## Main results

* `PathAdaptedAt.fixFlip`: fixing the `n`-th flip of an `(n + 1)`-adapted function leaves an
  `n`-adapted function.
* `PathAdaptedAt.mono`: an `m`-adapted function is `n`-adapted for `m ≤ n`.
* `repr_one_step`: if `M` and `S` satisfy the node-average condition with weight `q` and `S` is
  nondegenerate at every node, then `M_{n+1} − M_n = hedgeRatio M S n ω · (S_{n+1} − S_n)`.

## Tags

coin-flip paths, node average, delta hedge, binomial filtration, one-period hedge,
conditional expectation on a tree, MSC 91G20, MSC 60G42, JEL G13
-/

@[expose] public section

namespace MathFin

/-- A real function of an infinite coin-flip path is **`n`-adapted** when it depends only on the
first `n` flips `ω 0, …, ω (n−1)`. -/
def PathAdaptedAt (n : ℕ) (X : (ℕ → Bool) → ℝ) : Prop :=
  ∀ ω ω' : ℕ → Bool, (∀ i, i < n → ω i = ω' i) → X ω = X ω'

/-- Fixing the `n`-th flip of a function of the first `n + 1` flips leaves a function of the
first `n`. -/
lemma PathAdaptedAt.fixFlip {n : ℕ} {f : (ℕ → Bool) → ℝ} (hf : PathAdaptedAt (n + 1) f)
    (b : Bool) :
    PathAdaptedAt n fun ω ↦ f (Function.update ω n b) := fun ω ω' h ↦
  hf _ _ fun i hi ↦ by
    rcases eq_or_ne i n with rfl | hin
    · simp
    · rw [Function.update_of_ne hin, Function.update_of_ne hin]
      exact h i (by omega)

/-- A function of the first `m` flips is a function of the first `n`, for `m ≤ n`. -/
lemma PathAdaptedAt.mono {m n : ℕ} {X : (ℕ → Bool) → ℝ} (h : PathAdaptedAt m X)
    (hmn : m ≤ n) : PathAdaptedAt n X :=
  fun ω ω' hω ↦ h ω ω' fun i hi ↦ hω i (hi.trans_le hmn)

variable {q : ℝ} {M S : ℕ → (ℕ → Bool) → ℝ}

/-- The **node-wise hedge ratio** (discrete delta): the change in `M` over the change in `S`
across the up/down children of the level-`n` node carrying path `ω`. -/
noncomputable def hedgeRatio (M S : ℕ → (ℕ → Bool) → ℝ) (n : ℕ) (ω : ℕ → Bool) : ℝ :=
  (M (n + 1) (Function.update ω n true) - M (n + 1) (Function.update ω n false)) /
    (S (n + 1) (Function.update ω n true) - S (n + 1) (Function.update ω n false))

/-- **One-step representation (the node-wise delta hedge).** Under the risk-neutral one-step
condition for `M` and `S` and non-degeneracy of `S`'s branching, the one-period change in `M`
equals the hedge ratio times the one-period change in `S`, on every path. -/
theorem repr_one_step
    (hM_mart : ∀ n ω, q * M (n + 1) (Function.update ω n true)
        + (1 - q) * M (n + 1) (Function.update ω n false) = M n ω)
    (hS_mart : ∀ n ω, q * S (n + 1) (Function.update ω n true)
        + (1 - q) * S (n + 1) (Function.update ω n false) = S n ω)
    (hS_nondeg : ∀ n ω, S (n + 1) (Function.update ω n true)
        ≠ S (n + 1) (Function.update ω n false))
    (n : ℕ) (ω : ℕ → Bool) :
    M (n + 1) ω - M n ω = hedgeRatio M S n ω * (S (n + 1) ω - S n ω) := by
  have hne : S (n + 1) (Function.update ω n true) - S (n + 1) (Function.update ω n false) ≠ 0 :=
    sub_ne_zero.mpr (hS_nondeg n ω)
  rw [hedgeRatio, ← hM_mart n ω, ← hS_mart n ω]
  by_cases hb : ω n = true
  · have hωeq : Function.update ω n true = ω := by
      conv_rhs => rw [← Function.update_eq_self n ω]
      rw [hb]
    rw [hωeq] at hne ⊢
    field_simp
    ring
  · have hbf : ω n = false := by simpa using hb
    have hωeq : Function.update ω n false = ω := by
      conv_rhs => rw [← Function.update_eq_self n ω]
      rw [hbf]
    rw [hωeq] at hne ⊢
    field_simp
    ring

end MathFin
