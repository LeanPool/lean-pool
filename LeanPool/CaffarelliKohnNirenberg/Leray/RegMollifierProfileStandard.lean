/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMollifierGeneral
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# A standard mollifier profile

The regularization of `thm:regularised` fixes one smooth, compactly supported,
radial, nonnegative kernel of unit mass supported in the unit ball
(`lem:reg-mollifier-bounds`). This file supplies one such kernel: the
normalization of `x ↦ expNegInvGlue (1 - 4‖x‖²)`, which is smooth, radial,
nonnegative and supported in the closed ball of radius `1/2`.
-/

public section

open MeasureTheory Set Metric
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The unnormalized radial bump `x ↦ expNegInvGlue (1 - 4‖x‖²)`. -/
@[expose]
def standardRegBump (x : L2Vec3) : ℝ :=
  expNegInvGlue (1 - 4 * ‖x‖ ^ 2)

theorem standardRegBump_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) standardRegBump :=
  expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_const.mul (contDiff_norm_sq ℝ)))

private theorem standardRegBump_eq_zero {x : L2Vec3} (hx : 1 / 2 ≤ ‖x‖) :
    standardRegBump x = 0 := by
  apply expNegInvGlue.zero_of_nonpos
  nlinarith only [hx, norm_nonneg x]

private theorem standardRegBump_support_subset :
    Function.support standardRegBump ⊆ closedBall (0 : L2Vec3) (1 / 2) := by
  intro x hx
  rw [mem_closedBall, dist_zero_right]
  by_contra hlt
  exact hx (standardRegBump_eq_zero (le_of_lt (not_le.mp hlt)))

theorem standardRegBump_tsupport_subset :
    tsupport standardRegBump ⊆ closedBall (0 : L2Vec3) (1 / 2) :=
  closure_minimal standardRegBump_support_subset isClosed_closedBall

theorem standardRegBump_hasCompactSupport :
    HasCompactSupport standardRegBump :=
  (isCompact_closedBall (0 : L2Vec3) (1 / 2)).of_isClosed_subset
    (isClosed_tsupport _) standardRegBump_tsupport_subset

theorem standardRegBump_nonneg (x : L2Vec3) : 0 ≤ standardRegBump x :=
  expNegInvGlue.nonneg _

theorem standardRegBump_integral_pos :
    0 < ∫ x : L2Vec3, standardRegBump x := by
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    standardRegBump_contDiff.continuous standardRegBump_hasCompactSupport
    standardRegBump_nonneg (x := 0) ?_
  apply ne_of_gt
  apply expNegInvGlue.pos_of_pos
  simp

/-- The standard mollifier profile: the unit-mass normalization of the
radial bump `x ↦ expNegInvGlue (1 - 4‖x‖²)`, supported in the closed ball of
radius `1/2`. -/
@[expose]
def standardRegMollifierProfile : RegMollifierProfile :=
  let c : ℝ := (∫ x : L2Vec3, standardRegBump x)⁻¹
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => c * standardRegBump x) :=
    contDiff_const.mul standardRegBump_contDiff
  have hcompact : HasCompactSupport (fun x => c * standardRegBump x) :=
    standardRegBump_hasCompactSupport.mul_left
  { rho := hcompact.toSchwartzMap hsmooth
    smooth := hsmooth
    compact := hcompact
    support_unit := by
      intro x hx
      have hx' : x ∈ tsupport standardRegBump :=
        tsupport_mul_subset_right (f := fun _ : L2Vec3 => c) hx
      have hle := standardRegBump_tsupport_subset hx'
      rw [mem_closedBall, dist_zero_right] at hle
      rw [mem_ball, dist_zero_right]
      linarith only [hle]
    radial := by
      intro x y hxy
      change c * standardRegBump x = c * standardRegBump y
      simp only [standardRegBump, hxy]
    nonneg := by
      intro x
      change 0 ≤ c * standardRegBump x
      exact mul_nonneg (inv_nonneg.mpr standardRegBump_integral_pos.le)
        (standardRegBump_nonneg x)
    integral_eq_one := by
      change ∫ x : L2Vec3, c * standardRegBump x = 1
      rw [integral_const_mul]
      exact inv_mul_cancel₀ standardRegBump_integral_pos.ne' }

end CKN.Leray

end
