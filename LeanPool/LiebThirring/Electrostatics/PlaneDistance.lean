/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.Plane
public import LeanPool.LiebThirring.Defs.Coulomb

/-!
# Distance from a point to a parametrized affine plane

The perpendicular foot on a plane with unit normal.

The nonnegative height of a point above a plane with unit normal.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace LiebThirring

/-- The perpendicular foot on a plane with unit normal. -/
noncomputable def planeFoot (n b x : Position) : Position :=
  x - inner ℝ n (x - b) • n

/-- The nonnegative height of a point above a plane with unit normal. -/
noncomputable def planeHeight (n b x : Position) : ℝ :=
  |inner ℝ n (x - b)|

theorem planeHeight_nonneg (n b x : Position) : 0 ≤ planeHeight n b x :=
  abs_nonneg _

/-- The perpendicular foot satisfies the literal plane equation. -/
theorem planeFoot_mem (n b x : Position) (hn : ‖n‖ = 1) :
    planeFoot n b x ∈ affinePlane n b := by
  rw [mem_affinePlane]
  have hn' : inner ℝ n n = 1 := by
    rw [real_inner_self_eq_norm_sq, hn]
    norm_num
  have he : planeFoot n b x - b = (x - b) - inner ℝ n (x - b) • n := by
    simp only [planeFoot]
    abel
  rw [he, inner_sub_right, inner_smul_right, hn', mul_one, sub_self]

/-- The centre-to-foot vector is the signed height times the unit normal. -/
theorem sub_planeFoot (n b x : Position) :
    x - planeFoot n b x = inner ℝ n (x - b) • n := by
  simp only [planeFoot, sub_sub_cancel]

/-- Every vector in the plane is perpendicular to its centre-to-foot vector. -/
theorem inner_sub_planeFoot_sub_eq_zero (n b x y : Position) (hn : ‖n‖ = 1)
    (hy : y ∈ affinePlane n b) :
    inner ℝ (x - planeFoot n b x) (planeFoot n b x - y) = 0 := by
  have hp := planeFoot_mem n b x hn
  rw [mem_affinePlane] at hp hy
  have he : planeFoot n b x - y = (planeFoot n b x - b) - (y - b) := by abel
  have horth : inner ℝ n (planeFoot n b x - y) = 0 := by
    rw [he, inner_sub_right, hp, hy, sub_self]
  rw [sub_planeFoot, inner_smul_left, horth, mul_zero]

/-- Pythagoras for the perpendicular foot and any point of the plane. -/
theorem norm_sub_sq_eq_planeFoot (n b x y : Position) (hn : ‖n‖ = 1)
    (hy : y ∈ affinePlane n b) :
    ‖x - y‖ ^ 2 = ‖planeFoot n b x - y‖ ^ 2 + planeHeight n b x ^ 2 := by
  have he : x - y = (x - planeFoot n b x) + (planeFoot n b x - y) := by abel
  rw [he, norm_add_sq_real,
    inner_sub_planeFoot_sub_eq_zero n b x y hn hy, mul_zero, add_zero,
    sub_planeFoot, norm_smul, hn]
  simp only [Real.norm_eq_abs, mul_one, planeHeight]
  exact add_comm _ _

/-- Rebase an orthonormal frame at the perpendicular foot of the centre. -/
noncomputable def planeFrameAtFoot (n b x : Position) (hn : ‖n‖ = 1)
    (F : PlaneFrame (affinePlane n b)) : PlaneFrame (affinePlane n b) :=
  (AffineIsometryEquiv.constVAdd ℝ Planar
    (F.symm ⟨planeFoot n b x, planeFoot_mem n b x hn⟩)).trans F

@[simp] theorem planeFrameAtFoot_zero (n b x : Position) (hn : ‖n‖ = 1)
    (F : PlaneFrame (affinePlane n b)) :
    (planeFrameAtFoot n b x hn F 0 : Position) = planeFoot n b x := by
  simp [planeFrameAtFoot]

/-- Radial planar coordinates give the exact squared distance, including off-plane centres. -/
theorem norm_sub_planeFrameAtFoot_sq (n b x : Position) (hn : ‖n‖ = 1)
    (F : PlaneFrame (affinePlane n b)) (q : Planar) :
    ‖x - (planeFrameAtFoot n b x hn F q : Position)‖ ^ 2 =
      ‖q‖ ^ 2 + planeHeight n b x ^ 2 := by
  let G := planeFrameAtFoot n b x hn F
  have hd : ‖planeFoot n b x - (G q : Position)‖ = ‖q‖ := by
    rw [← planeFrameAtFoot_zero n b x hn F]
    change ‖(G 0 : Position) - (G q : Position)‖ = ‖q‖
    rw [← dist_eq_norm]
    change dist (G 0) (G q) = ‖q‖
    rw [G.dist_map, dist_zero_left]
  rw [norm_sub_sq_eq_planeFoot n b x _ hn (G q).property, hd]

/-- The literal distance in a foot-based frame is the radial square-root expression. -/
theorem norm_sub_planeFrameAtFoot_eq_sqrt (n b x : Position) (hn : ‖n‖ = 1)
    (F : PlaneFrame (affinePlane n b)) (q : Planar) :
    ‖x - (planeFrameAtFoot n b x hn F q : Position)‖ =
      Real.sqrt (‖q‖ ^ 2 + planeHeight n b x ^ 2) := by
  rw [← norm_sub_planeFrameAtFoot_sq n b x hn F q, Real.sqrt_sq (norm_nonneg _)]

/-- Exact radial Coulomb expression; when both radius and height vanish its value is infinity. -/
theorem coulombKernel_planeFrameAtFoot (n b x : Position) (hn : ‖n‖ = 1)
    (F : PlaneFrame (affinePlane n b)) (q : Planar) :
    coulombKernel x (planeFrameAtFoot n b x hn F q : Position) =
      (ENNReal.ofReal (Real.sqrt (‖q‖ ^ 2 + planeHeight n b x ^ 2)))⁻¹ := by
  rw [coulombKernel, norm_sub_planeFrameAtFoot_eq_sqrt]

/-- Frame independence permits the perpendicular-foot chart for all measurable integrands. -/
theorem lintegral_planeMeasure_atFoot (n b x : Position) (hn : ‖n‖ = 1)
    (F : PlaneFrame (affinePlane n b)) (f : Position → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y, f y ∂planeMeasure F =
      ∫⁻ q, f (planeFrameAtFoot n b x hn F q : Position) := by
  rw [planeMeasure_eq F (planeFrameAtFoot n b x hn F), lintegral_planeMeasure _ f hf]

/-- The ambient ball truncation becomes its exact radial square-root cutoff.
No positivity condition on the radius and no restriction on the centre is needed. -/
theorem lintegral_coulombKernel_ball_planeMeasure (n b x : Position) (hn : ‖n‖ = 1)
    (F : PlaneFrame (affinePlane n b)) (ε : ℝ) :
    ∫⁻ y in Metric.ball x ε, coulombKernel x y ∂planeMeasure F =
      ∫⁻ q : Planar, if Real.sqrt (‖q‖ ^ 2 + planeHeight n b x ^ 2) < ε then
        (ENNReal.ofReal (Real.sqrt (‖q‖ ^ 2 + planeHeight n b x ^ 2)))⁻¹ else 0 := by
  classical
  have hf : Measurable (coulombKernel x) :=
    ((measurable_const.sub measurable_id).norm.ennreal_ofReal).inv
  rw [← lintegral_indicator measurableSet_ball,
    lintegral_planeMeasure_atFoot n b x hn F _ (hf.indicator measurableSet_ball)]
  apply lintegral_congr
  intro q
  rw [Set.indicator_apply]
  simp only [Metric.mem_ball, dist_eq_norm, norm_sub_rev,
    norm_sub_planeFrameAtFoot_eq_sqrt, coulombKernel_planeFrameAtFoot]

end LiebThirring

end
