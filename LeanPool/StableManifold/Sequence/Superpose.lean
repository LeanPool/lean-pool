/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Adapted for Lean Pool.

public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# The superposition operator on bounded sequences

The Lyapunov–Perron method works in the Banach space `ℕ →ᵇ E` of bounded sequences (bounded
continuous functions on the discrete space `ℕ`, with the sup norm). A map `φ : E → G` acts on it
by composition, `x ↦ φ ∘ x` (the superposition, or Nemytskii, operator).

* `StableManifold.superpose φ`: the superposition operator, `superpose φ x n = φ (x n)` whenever
  `φ ∘ x` is bounded (`superpose_apply_of_bound`), in particular for every `x` when `φ` is
  Lipschitz (`superpose_apply_of_lipschitzWith`) or continuous on a proper space
  (`superpose_apply`); it is `0` otherwise, a junk value never used;
* `StableManifold.lipschitzWith_superpose`: a `K`-Lipschitz `φ` gives a `K`-Lipschitz operator;
* `StableManifold.continuous_superpose`: a continuous `φ` on a proper space gives a continuous
  operator.

## Proofs

* `superpose_apply_of_bound`: unfold the definition (`dite_eq_left`).
* `superpose_apply_of_lipschitzWith`: `‖φ (x n)‖ ≤ ‖φ 0‖ + K ‖x‖` (`LipschitzWith.dist_le_mul`,
  `BoundedContinuousFunction.norm_coe_le_norm`).
* `superpose_apply`: `φ` is bounded on the compact ball `closedBall 0 ‖x‖`, which contains every
  `x n` (`isCompact_closedBall`, `IsCompact.exists_bound_of_continuousOn`).
* `superpose_zero`: `φ (0 n) = φ 0 = 0` for every `n`.
* `lipschitzWith_superpose`: `dist (φ (x n)) (φ (y n)) ≤ K dist (x n) (y n) ≤ K dist x y`
  (`BoundedContinuousFunction.dist_coe_le_dist`), then `BoundedContinuousFunction.dist_le` and
  `LipschitzWith.of_dist_le_mul`.
* `continuous_superpose`: `φ` is uniformly continuous on the compact ball `closedBall 0 (‖x‖ + 1)`
  (`IsCompact.uniformContinuousOn_of_continuous`), which contains the values of `x` and of every
  `y` with `dist y x < 1`; with `δ` for `ε / 2`, `dist (superpose φ y) (superpose φ x) ≤ ε / 2`
  once `dist y x < min δ 1` (`Metric.continuous_iff`, `BoundedContinuousFunction.dist_le`).
-/

@[expose] public section

open Filter Topology Metric
open scoped NNReal

namespace StableManifold

open BoundedContinuousFunction

section Superpose

variable {E G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup G]

open Classical in
/-- The **superposition operator** of `φ` on bounded sequences: `x ↦ φ ∘ x` when `φ ∘ x` is
bounded (always the case when `φ` is Lipschitz, or continuous on a proper space); `0` otherwise,
a junk value. -/
noncomputable def superpose (φ : E → G) (x : ℕ →ᵇ E) : ℕ →ᵇ G :=
  if h : ∃ C, ∀ n, ‖φ (x n)‖ ≤ C then
    ofNormedAddCommGroupDiscrete (fun n ↦ φ (x n)) h.choose h.choose_spec
  else 0

theorem superpose_apply_of_bound {φ : E → G} {x : ℕ →ᵇ E} (h : ∃ C, ∀ n, ‖φ (x n)‖ ≤ C)
    (n : ℕ) : superpose φ x n = φ (x n) := by
  rw [superpose, dite_eq_left h]
  rfl

/-- For a Lipschitz `φ`, `superpose φ x n = φ (x n)` for every bounded sequence `x`. -/
theorem superpose_apply_of_lipschitzWith {φ : E → G} {K : ℝ≥0} (hφ : LipschitzWith K φ)
    (x : ℕ →ᵇ E) (n : ℕ) : superpose φ x n = φ (x n) := by
  refine superpose_apply_of_bound ⟨‖φ 0‖ + K * ‖x‖, fun m ↦ ?_⟩ n
  calc ‖φ (x m)‖ ≤ ‖φ 0‖ + ‖φ (x m) - φ 0‖ := norm_le_insert' _ _
    _ ≤ ‖φ 0‖ + K * ‖x m‖ := by
        gcongr
        simpa [dist_eq_norm] using hφ.dist_le_mul (x m) 0
    _ ≤ ‖φ 0‖ + K * ‖x‖ := by gcongr; exact x.norm_coe_le_norm m

/-- For a continuous `φ` on a proper space, `superpose φ x n = φ (x n)` for every bounded sequence
`x`. -/
theorem superpose_apply [ProperSpace E] {φ : E → G} (hφ : Continuous φ) (x : ℕ →ᵇ E) (n : ℕ) :
    superpose φ x n = φ (x n) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) ‖x‖).exists_bound_of_continuousOn
    hφ.continuousOn
  exact superpose_apply_of_bound
    ⟨C, fun m ↦ hC _ (mem_closedBall_zero_iff.2 (x.norm_coe_le_norm m))⟩ n

theorem superpose_zero {φ : E → G} (hφ : φ 0 = 0) : superpose φ 0 = 0 := by
  ext n
  rw [superpose_apply_of_bound ⟨0, fun _ ↦ by simp [hφ]⟩]
  simp [hφ]

/-- A `K`-Lipschitz `φ` gives a `K`-Lipschitz superposition operator. -/
theorem lipschitzWith_superpose {φ : E → G} {K : ℝ≥0} (hφ : LipschitzWith K φ) :
    LipschitzWith K (superpose φ) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ (dist_le (by positivity)).2 fun n ↦ ?_
  rw [superpose_apply_of_lipschitzWith hφ, superpose_apply_of_lipschitzWith hφ]
  exact (hφ.dist_le_mul _ _).trans (by gcongr; exact dist_coe_le_dist n)

/-- A continuous `φ` on a proper space gives a continuous superposition operator.

Proof: `φ` is uniformly continuous on the compact ball `closedBall 0 (‖x‖ + 1)`, which contains
the values of all sequences `1`-close to `x`. -/
theorem continuous_superpose [ProperSpace E] {φ : E → G} (hφ : Continuous φ) :
    Continuous (superpose φ) := by
  refine Metric.continuous_iff.2 fun x ε hε ↦ ?_
  obtain ⟨δ, hδ, hφδ⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_closedBall (0 : E) (‖x‖ + 1)).uniformContinuousOn_of_continuous hφ.continuousOn)
    (ε / 2) (half_pos hε)
  refine ⟨min δ 1, lt_min hδ one_pos, fun y hy ↦ ?_⟩
  refine lt_of_le_of_lt ((dist_le (half_pos hε).le).2 fun n ↦ ?_) (half_lt_self hε)
  rw [superpose_apply hφ, superpose_apply hφ]
  have hyx : dist (y n) (x n) < min δ 1 := (dist_coe_le_dist n).trans_lt hy
  have hx : x n ∈ closedBall (0 : E) (‖x‖ + 1) :=
    mem_closedBall_zero_iff.2 ((x.norm_coe_le_norm n).trans (le_add_of_nonneg_right zero_le_one))
  have hy' : y n ∈ closedBall (0 : E) (‖x‖ + 1) := by
    rw [mem_closedBall_zero_iff]
    calc ‖y n‖ ≤ ‖x n‖ + dist (y n) (x n) := by
          rw [dist_eq_norm]; exact norm_le_insert' _ _
      _ ≤ ‖x‖ + 1 := add_le_add (x.norm_coe_le_norm n) (hyx.le.trans (min_le_right _ _))
  exact (hφδ _ hy' _ hx (hyx.trans_le (min_le_left _ _))).le

end Superpose

end StableManifold
