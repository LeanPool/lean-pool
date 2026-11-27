/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Algebra.Order.Round
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# The `ℤ^m`-periodization of a function supported in a small ball

For `g : ℝ^m → ℝ`, `supPeriodize g x = sup_{k ∈ ℤ^m} g (x + k)`. When `g ≥ 0` vanishes outside
the ball `B_r (x₀)` (sup norm) with `r < 1/2`, the translates `B_r (x₀ − k)` are disjoint, and
`supPeriodize g` is the `ℤ^m`-periodic function equal to `g (· + k)` near every point `x` with
`‖x + k − x₀‖ ≤ 1/2`.

* `supPeriodize_periodic`: `supPeriodize g` is `ℤ^m`-periodic;
* `exists_norm_add_intVec_sub_le_half`: every `x` has a `k ∈ ℤ^m` with `‖x + k − x₀‖ ≤ 1/2`;
* `one_le_norm_intVec_sub`: distinct points of `ℤ^m` are at distance at least `1`;
* `supPeriodize_eventuallyEq`, `supPeriodize_eq`: near such an `x`, `supPeriodize g = g (· + k)`;
* `lipschitzWith_supPeriodize`: `supPeriodize g` is `K`-Lipschitz if `g` is (and bounded above).

These facts are elementary.
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace CalculusOfVariations

variable {m : ℕ}

/-- The `ℤ^m`-periodization `x ↦ sup_{k ∈ ℤ^m} g (x + k)` of `g : ℝ^m → ℝ`. -/
def supPeriodize (g : (Fin m → ℝ) → ℝ) (x : Fin m → ℝ) : ℝ :=
  ⨆ k : Fin m → ℤ, g (x + fun i => (k i : ℝ))

/-- `supPeriodize g` is `ℤ^m`-periodic: the translation by `k` permutes the translates. -/
theorem supPeriodize_periodic (g : (Fin m → ℝ) → ℝ) (x : Fin m → ℝ) (k : Fin m → ℤ) :
    supPeriodize g (x + fun i => (k i : ℝ)) = supPeriodize g x := by
  unfold supPeriodize
  refine (Equiv.addLeft k).iSup_congr fun k' => ?_
  congr 1
  ext i
  simp only [Equiv.coe_addLeft, Pi.add_apply, Int.cast_add]
  ring

/-- Every `x ∈ ℝ^m` has an integer translate within `1/2` of `x₀` (sup norm). -/
theorem exists_norm_add_intVec_sub_le_half (x₀ x : Fin m → ℝ) :
    ∃ k : Fin m → ℤ, ‖x + (fun i => (k i : ℝ)) - x₀‖ ≤ 1 / 2 := by
  refine ⟨fun i => round (x₀ i - x i), (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_⟩
  have h := abs_sub_round (x₀ i - x i)
  rw [abs_sub_comm] at h
  simp only [Pi.add_apply, Pi.sub_apply, Real.norm_eq_abs]
  calc |x i + (round (x₀ i - x i) : ℝ) - x₀ i| = |(round (x₀ i - x i) : ℝ) - (x₀ i - x i)| := by
        ring_nf
    _ ≤ 1 / 2 := h

/-- Distinct points of `ℤ^m` are at distance at least `1` (sup norm). -/
theorem one_le_norm_intVec_sub {k k' : Fin m → ℤ} (h : k ≠ k') :
    1 ≤ ‖(fun i => (k i : ℝ)) - fun i => (k' i : ℝ)‖ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h
  calc (1 : ℝ) ≤ |(k i : ℝ) - k' i| := by
        have : (1 : ℤ) ≤ |k i - k' i| := Int.one_le_abs (sub_ne_zero.2 hi)
        exact_mod_cast this
    _ = ‖((fun i => (k i : ℝ)) - fun i => (k' i : ℝ)) i‖ := by simp [Real.norm_eq_abs]
    _ ≤ _ := norm_le_pi_norm _ i

variable {g : (Fin m → ℝ) → ℝ} {x₀ : Fin m → ℝ} {r : ℝ}

/-- If `g ≥ 0` vanishes outside `B_r (x₀)`, `r < 1/2`, and `‖x + k − x₀‖ ≤ 1/2`, then
`supPeriodize g = g (· + k)` near `x`: the other translates vanish there. -/
theorem supPeriodize_eventuallyEq (hg0 : ∀ x, 0 ≤ g x)
    (hsupp : ∀ x, r ≤ ‖x - x₀‖ → g x = 0) (hr : r < 1 / 2) {x : Fin m → ℝ} {k : Fin m → ℤ}
    (hk : ‖x + (fun i => (k i : ℝ)) - x₀‖ ≤ 1 / 2) :
    supPeriodize g =ᶠ[𝓝 x] fun y => g (y + fun i => (k i : ℝ)) := by
  filter_upwards [Metric.ball_mem_nhds x (show (0 : ℝ) < 1 / 2 - r by linarith)] with y hy
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have hle : ∀ k' : Fin m → ℤ, g (y + fun i => (k' i : ℝ)) ≤ g (y + fun i => (k i : ℝ)) := by
    intro k'
    by_cases hk' : k' = k
    · rw [hk']
    rw [hsupp _ ?_]
    · exact hg0 _
    have h1 := one_le_norm_intVec_sub hk'
    have h2 : ‖y + (fun i => (k i : ℝ)) - x₀‖ ≤ ‖y - x‖ + ‖x + (fun i => (k i : ℝ)) - x₀‖ := by
      calc _ = ‖(y - x) + (x + (fun i => (k i : ℝ)) - x₀)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have h3 : ‖(fun i => (k' i : ℝ)) - fun i => (k i : ℝ)‖ ≤
        ‖y + (fun i => (k' i : ℝ)) - x₀‖ + ‖y + (fun i => (k i : ℝ)) - x₀‖ := by
      calc _ = ‖(y + (fun i => (k' i : ℝ)) - x₀) - (y + (fun i => (k i : ℝ)) - x₀)‖ := by
            congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    linarith
  exact le_antisymm (ciSup_le hle)
    (le_ciSup (f := fun k' : Fin m → ℤ => g (y + fun i => (k' i : ℝ)))
      ⟨_, by rintro _ ⟨k', rfl⟩; exact hle k'⟩ k)

/-- If `g ≥ 0` vanishes outside `B_r (x₀)`, `r < 1/2`, and `‖x + k − x₀‖ ≤ 1/2`, then
`supPeriodize g x = g (x + k)`. -/
theorem supPeriodize_eq (hg0 : ∀ x, 0 ≤ g x)
    (hsupp : ∀ x, r ≤ ‖x - x₀‖ → g x = 0) (hr : r < 1 / 2) {x : Fin m → ℝ} {k : Fin m → ℤ}
    (hk : ‖x + (fun i => (k i : ℝ)) - x₀‖ ≤ 1 / 2) :
    supPeriodize g x = g (x + fun i => (k i : ℝ)) :=
  (supPeriodize_eventuallyEq hg0 hsupp hr hk).eq_of_nhds

/-- The periodization of a `K`-Lipschitz function bounded above is `K`-Lipschitz. -/
theorem lipschitzWith_supPeriodize {K : NNReal} (hg : LipschitzWith K g) {M : ℝ}
    (hM : ∀ x, g x ≤ M) : LipschitzWith K (supPeriodize g) := by
  refine LipschitzWith.of_le_add_mul K fun x y => ciSup_le fun k => ?_
  have hb : BddAbove (Set.range fun k : Fin m → ℤ => g (y + fun i => (k i : ℝ))) :=
    ⟨M, by rintro _ ⟨k, rfl⟩; exact hM _⟩
  calc g (x + fun i => (k i : ℝ))
      ≤ g (y + fun i => (k i : ℝ)) + K * dist (x + fun i => (k i : ℝ)) (y + fun i => (k i : ℝ)) :=
        hg.le_add_mul _ _
    _ ≤ supPeriodize g y + K * dist x y := by
        rw [dist_eq_norm, dist_eq_norm, add_sub_add_right_eq_sub]
        gcongr
        exact le_ciSup hb k

end CalculusOfVariations
