/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.Continuity
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.PenalizedNormalizedTail

/-!
# PenalizedInterchangeGeometry

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Cube geometry for the exterior-penalization interchange

The support cube is surrounded by a fixed compact collar inside the next
exhaustion cube.  Every point beyond that collar has a unit Euclidean ball
disjoint from the support, and unit balls around the inner cube fit in its
successor.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport Set

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The closed sup-norm collar used around the support cube. -/
def interchangeCollar (d v : ℕ) : Set (Vec d) :=
  Metric.closedBall 0 ((3 : ℝ) ^ v + 1)

/-- The support cube lies in its closed collar. -/
theorem wholeSpaceCube_subset_interchangeCollar (d v : ℕ) :
    wholeSpaceCube d v ⊆ interchangeCollar d v := by
  intro x hx
  rw [interchangeCollar, Metric.mem_closedBall, dist_zero_right]
  rw [mem_wholeSpaceCube_iff] at hx
  have hnorm : ‖x‖ ≤ (3 : ℝ) ^ v := by
    refine (pi_norm_le_iff_of_nonneg (pow_nonneg (by norm_num) v)).2 ?_
    intro i
    simpa only [Real.norm_eq_abs] using (abs_lt.2 (hx i)).le
  exact hnorm.trans (le_add_of_nonneg_right zero_le_one)

/-- The closed collar is compact. -/
theorem isCompact_interchangeCollar (d v : ℕ) :
    IsCompact (interchangeCollar d v) := by
  exact ProperSpace.isCompact_closedBall 0 ((3 : ℝ) ^ v + 1)

/-- The closed collar lies strictly inside the next exhaustion cube. -/
theorem interchangeCollar_subset_wholeSpaceCube_succ (d v : ℕ) :
    interchangeCollar d v ⊆ wholeSpaceCube d (v + 1) := by
  intro x hx
  rw [interchangeCollar, Metric.mem_closedBall, dist_zero_right] at hx
  rw [mem_wholeSpaceCube_iff]
  have hp1 : (1 : ℝ) ≤ 3 ^ v := one_le_pow₀ (by norm_num)
  have hgap : (3 : ℝ) ^ v + 1 < (3 : ℝ) ^ (v + 1) := by
    rw [pow_succ]
    linarith only [hp1]
  intro i
  have hi : |x i| ≤ (3 : ℝ) ^ v + 1 :=
    (norm_le_pi_norm x i).trans hx
  exact abs_lt.1 (hi.trans_lt hgap)

omit [NeZero d] in
/-- A point beyond the collar has a unit Euclidean ball disjoint from the
support cube. -/
theorem disjoint_unitBall_wholeSpaceCube_of_notMem_interchangeCollar
    (v : ℕ) {x : Vec d} (hx : x ∉ interchangeCollar d v) :
    Disjoint (euclideanBall x 1) (wholeSpaceCube d v) := by
  rw [Set.disjoint_left]
  intro y hyBall hyCube
  have hxnorm : (3 : ℝ) ^ v + 1 < ‖x‖ := by
    rw [interchangeCollar, Metric.mem_closedBall, dist_zero_right] at hx
    exact lt_of_not_ge hx
  have hynorm : ‖y‖ < (3 : ℝ) ^ v := by
    rw [mem_wholeSpaceCube_iff] at hyCube
    exact (pi_norm_lt_iff (pow_pos (by norm_num) v)).2 fun i ↦ by
      simpa only [Real.norm_eq_abs] using abs_lt.2 (hyCube i)
  have hdEuclid : euclideanNorm (x - y) < 1 := by
    have h := Decay.euclideanNorm_sub_lt_of_mem_euclideanBall
      (by norm_num : (0 : ℝ) ≤ 1) hyBall
    calc
      euclideanNorm (x - y) = euclideanNorm (-(y - x)) := by
        congr 1
        funext i
        simp only [Pi.sub_apply, Pi.neg_apply]
        ring
      _ = euclideanNorm (y - x) := euclideanNorm_neg (y - x)
      _ < 1 := h
  have hdNorm : ‖x - y‖ < 1 :=
    (HCPolySupport.norm_le_euclideanNorm (x - y)).trans_lt hdEuclid
  have htri : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
    have heq : x = (x - y) + y := by
      funext i
      simp only [Pi.sub_apply, Pi.add_apply]
      ring
    calc
      ‖x‖ = ‖(x - y) + y‖ := congrArg norm heq
      _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le (x - y) y
  linarith only [hxnorm, hynorm, hdNorm, htri]

omit [NeZero d] in
/-- A unit Euclidean ball around the `m`-th cube lies in the successor cube. -/
theorem unitBall_subset_wholeSpaceCube_succ {m : ℕ} {x : Vec d}
    (hx : x ∈ wholeSpaceCube d m) :
    euclideanBall x 1 ⊆ wholeSpaceCube d (m + 1) := by
  intro y hy
  rw [mem_wholeSpaceCube_iff] at hx ⊢
  have hdist := Decay.euclideanNorm_sub_lt_of_mem_euclideanBall
    (by norm_num : (0 : ℝ) ≤ 1) hy
  have hp1 : (1 : ℝ) ≤ 3 ^ m := one_le_pow₀ (by norm_num)
  have hgap : (3 : ℝ) ^ m + 1 < (3 : ℝ) ^ (m + 1) := by
    rw [pow_succ]
    linarith only [hp1]
  intro i
  have hcoord : |y i - x i| < 1 :=
    (HCPolySupport.abs_coordinate_le_euclideanNorm (y - x) i).trans_lt hdist
  have hyabs : |y i| < (3 : ℝ) ^ m + 1 := by
    have htri : |y i| ≤ |y i - x i| + |x i| := by
      have h := abs_add_le (y i - x i) (x i)
      simpa only [sub_add_cancel] using h
    have hxabs : |x i| < (3 : ℝ) ^ m := abs_lt.2 (hx i)
    linarith only [htri, hcoord, hxabs]
  exact abs_lt.1 (hyabs.trans hgap)

end

end DivergenceFormProcess.Form
