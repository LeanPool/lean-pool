/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Extension.C1Boundary
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Analysis.InnerProductSpace.Calculus


/-!
# `C¹` boundary of the unit ball

Every theorem of this development on a bounded domain with `C¹` boundary has, until this file,
only the half space as an instance of its boundary hypothesis, and the half space is
unbounded. This file supplies the unit ball, so that the extension operator, the embeddings of
order `k`, global approximation, Rellich-Kondrachov on `H¹(Ω)` and the Poincaré inequality
with the mean subtracted all have a domain to be applied to.

The chart at a boundary point is the reflection in the hyperplane bisecting the point and the
south pole, which is a linear isometry sending the point to the pole and the ball to itself,
together with the graph of the lower hemisphere, cut off in the tangential directions so that
it is `C¹` on the whole space and independent of the vertical coordinate. On the ball of radius
one half about the pole every point has vertical coordinate below one half and tangential part
of norm below one half, so the cutoff is inactive, and the ball is the region above the graph
there because `‖y‖² = ‖y'‖² + y_d²` with `y_d < 0`.

## Main declarations

* `EllipticPdes.Extension.norm_sq_eq_tangential_add_sq`: the norm splits into the tangential
  part and the coordinate.
* `EllipticPdes.Extension.ballGraph`: the cut-off lower hemisphere.
* `EllipticPdes.Extension.ballChart`: the chart at a boundary point of the unit ball.
* `EllipticPdes.Extension.hasC1Boundary_ball`: the unit ball has `C¹` boundary.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §C.1 (p. 665);
Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Definition III.1.1.
-/

@[expose] public section

open Metric Set

noncomputable section

namespace EllipticPdes.Extension

variable {d : ℕ}

/-! ### The norm through the tangential projection -/

/-- **Norm split into the tangential part and the coordinate.** -/
theorem norm_sq_eq_tangential_add_sq (j : Fin d) (y : EuclideanSpace ℝ (Fin d)) :
    ‖y‖ ^ 2 = ‖tangential j y‖ ^ 2 + (y j) ^ 2 := by
  classical
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    Fintype.sum_eq_add_sum_compl j (fun i => ‖y i‖ ^ 2),
    Fintype.sum_eq_add_sum_compl j (fun i => ‖tangential j y i‖ ^ 2),
    tangential_coord, ite_eq_left rfl, norm_zero, zero_pow two_ne_zero, zero_add, Real.norm_eq_abs,
    sq_abs, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hij : i ≠ j := by simpa using hi
  rw [tangential_coord, ite_eq_right hij]

/-- The south pole has no tangential part. -/
theorem tangential_neg_single (j : Fin d) :
    tangential j (-(EuclideanSpace.single j (1 : ℝ))) = 0 := by
  ext i
  rw [tangential_coord]
  by_cases h : i = j <;> simp [h]

/-! ### The graph of the lower hemisphere -/

/-- The cutoff in the tangential directions: one on `[0, 1/4]`, zero from `1/2` on. -/
def ballBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The argument of the square root stays above one half. -/
theorem ballBump_mul_le {s : ℝ} (hs : 0 ≤ s) : ballBump s * s ≤ 1 / 2 := by
  by_cases h : s ≤ 1 / 2
  · calc ballBump s * s ≤ 1 * s := by gcongr; exact ballBump.le_one
      _ ≤ 1 / 2 := by linarith
  · have h0 : ballBump s = 0 := ballBump.zero_of_le_dist (by
      have hr : ballBump.rOut = 1 / 2 := rfl
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hs, hr]
      linarith)
    rw [h0, zero_mul]; norm_num

/-- The cutoff is inactive on `[0, 1/4]`. -/
theorem ballBump_eq_one {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1 / 4) : ballBump s = 1 :=
  ballBump.one_of_mem_closedBall (by
    rw [mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg hs]; exact hs')

/-- **Graph of the lower hemisphere**, cut off in the tangential directions so that it
is defined and `C¹` on the whole space. -/
def ballGraph (j : Fin d) (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  -Real.sqrt (1 - ballBump (‖tangential j y‖ ^ 2) * ‖tangential j y‖ ^ 2)

/-- Near the pole the graph is the lower hemisphere itself. -/
theorem ballGraph_eq_of_le (j : Fin d) {y : EuclideanSpace ℝ (Fin d)}
    (hy : ‖tangential j y‖ ^ 2 ≤ 1 / 4) :
    ballGraph j y = -Real.sqrt (1 - ‖tangential j y‖ ^ 2) := by
  rw [ballGraph, ballBump_eq_one (sq_nonneg _) hy, one_mul]

/-- The graph is `C¹`, the square root being taken of a quantity above one half. -/
theorem contDiff_ballGraph (j : Fin d) : ContDiff ℝ 1 (ballGraph j) := by
  have hs : ContDiff ℝ 1 fun y : EuclideanSpace ℝ (Fin d) => ‖tangential j y‖ ^ 2 :=
    (contDiff_norm_sq ℝ).comp (tangential j).contDiff
  have hχ : ContDiff ℝ 1 fun y : EuclideanSpace ℝ (Fin d) => ballBump (‖tangential j y‖ ^ 2) :=
    (ballBump.contDiff (n := 1)).comp hs
  have harg : ContDiff ℝ 1 fun y : EuclideanSpace ℝ (Fin d) =>
      1 - ballBump (‖tangential j y‖ ^ 2) * ‖tangential j y‖ ^ 2 :=
    contDiff_const.sub (hχ.mul hs)
  have hpos : ∀ y : EuclideanSpace ℝ (Fin d),
      1 - ballBump (‖tangential j y‖ ^ 2) * ‖tangential j y‖ ^ 2 ≠ 0 := fun y => by
    have := ballBump_mul_le (sq_nonneg ‖tangential j y‖)
    linarith
  refine ContDiff.neg ?_
  rw [contDiff_iff_contDiffAt]
  intro y
  exact harg.contDiffAt.sqrt (hpos y)

/-- The graph does not depend on the coordinate it is a graph in. -/
theorem indepCoord_ballGraph (j : Fin d) : IndepCoord j (ballGraph j) := by
  intro y t
  simp only [ballGraph, tangential_add_smul]

/-! ### The chart -/

/-- **Chart at a boundary point of the unit ball**: the reflection sending the point to
the south pole, the direction of the pole, the cut-off lower hemisphere, and radius one half. -/
def ballChart (hd : 0 < d) (x : EuclideanSpace ℝ (Fin d)) : C1Chart d where
  motion := Submodule.reflection
    (ℝ ∙ (x - (-(EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ)))))ᗮ
  dir := ⟨0, hd⟩
  graph := ballGraph ⟨0, hd⟩
  radius := 1 / 2
  radius_pos := by norm_num
  graph_contDiff := contDiff_ballGraph _
  graph_indep := indepCoord_ballGraph _

/-- The reflection sends the point to the pole. -/
theorem ballChart_motion_apply (hd : 0 < d) {x : EuclideanSpace ℝ (Fin d)} (hx : ‖x‖ = 1) :
    (ballChart hd x).motion x = -(EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ)) := by
  apply Submodule.reflection_sub
  rw [hx, norm_neg, PiLp.norm_single, norm_one]

/-- **Fit of the chart at its boundary point.** On the ball of radius one half
about the pole, membership of the unit ball is the inequality `y_d > -√(1 - ‖y'‖²)`. -/
theorem ballChart_fits (hd : 0 < d) {x : EuclideanSpace ℝ (Fin d)} (hx : ‖x‖ = 1) :
    (ballChart hd x).Fits (ball 0 1) x := by
  set j : Fin d := ⟨0, hd⟩ with hj
  set p : EuclideanSpace ℝ (Fin d) := -(EuclideanSpace.single j (1 : ℝ)) with hp
  have hpj : p j = -1 := by simp [hp]
  unfold C1Chart.Fits
  rw [ballChart_motion_apply hd hx]
  change (ballChart hd x).motion '' ball 0 1 ∩ ball p (1 / 2)
    = aboveGraph j (ballGraph j) ∩ ball p (1 / 2)
  rw [LinearIsometryEquiv.image_ball, LinearIsometryEquiv.map_zero]
  ext y
  simp only [mem_inter_iff, aboveGraph, mem_ofPred_eq, and_congr_left_iff]
  intro hy
  rw [mem_ball, dist_eq_norm] at hy
  -- the tangential part and the coordinate on the small ball
  have htan : tangential j y = tangential j (y - p) := by
    rw [map_sub, hp, tangential_neg_single, sub_zero]
  have htan_lt : ‖tangential j y‖ < 1 / 2 := by
    rw [htan]; exact lt_of_le_of_lt (norm_tangential_le j (y - p)) hy
  have hs : ‖tangential j y‖ ^ 2 ≤ 1 / 4 := by
    have h0 : 0 ≤ ‖tangential j y‖ := norm_nonneg _
    nlinarith
  have hyj : y j < -1 / 2 := by
    have h1 : |(y - p) j| ≤ ‖y - p‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (y - p) j
    have h2 : (y - p) j = y j - p j := rfl
    rw [h2, hpj] at h1
    have := (abs_lt.mp (lt_of_le_of_lt h1 hy)).2
    linarith
  rw [ballGraph_eq_of_le j hs, mem_ball, dist_zero_right,
    ← sq_lt_one_iff₀ (norm_nonneg y), norm_sq_eq_tangential_add_sq j y]
  have hpos : 0 < 1 - ‖tangential j y‖ ^ 2 := by linarith
  constructor
  · intro h
    have h' : (-(y j)) ^ 2 < 1 - ‖tangential j y‖ ^ 2 := by rw [neg_sq]; linarith
    have := (Real.lt_sqrt (by linarith)).mpr h'
    linarith
  · intro h
    have h' : -(y j) < Real.sqrt (1 - ‖tangential j y‖ ^ 2) := by linarith
    have := (Real.lt_sqrt (by linarith)).mp h'
    rw [neg_sq] at this
    linarith

/-- **`C¹` boundary of the unit ball.** Its boundary is the unit sphere, and every point of
the sphere has the chart above. -/
theorem hasC1Boundary_ball (hd : 0 < d) :
    HasC1Boundary (ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  intro x hx
  rw [frontier_ball (0 : EuclideanSpace ℝ (Fin d)) one_ne_zero, mem_sphere_zero_iff_norm] at hx
  exact ⟨ballChart hd x, ballChart_fits hd hx⟩

end EllipticPdes.Extension
