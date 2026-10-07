/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basis
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Basic
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The spatial mollifier of `lem:aniso:comparison`

The comparison argument mollifies in space with the standard family
`η_ε = ε^{-m} η(·/ε)`, where `η` is a fixed smooth nonnegative kernel of unit mass supported
in the unit ball. The profile `η` is the normalized bump kernel of the ambient library, and
the family is obtained from it by the explicit rescaling, so that the scaling identities
below are available.

The bounds recorded here are the two that the commutator estimate of DiPerna and Lions needs:
the kernel has unit mass and is supported in the ball of radius `ε`, and the integral of the
length of its gradient is `C_η/ε` with `C_η` the corresponding integral for the profile. The
ball is the one of the sup norm of `Vec m`, which is the norm carried by that type.
-/

public section

open CKN MeasureTheory

noncomputable section

namespace CIV

variable {m : ℕ}

/-! ### The fixed profile -/

/-- The fixed mollifier profile `η`: the normalized smooth bump of radius one on `Vec m`. -/
@[expose] def mollifierProfile (m : ℕ) : Vec m → ℝ := CKN.mollifier (d := m) 1 one_pos

theorem mollifierProfile_nonneg (x : Vec m) : 0 ≤ mollifierProfile m x :=
  CKN.mollifier_nonneg one_pos x

theorem contDiff_mollifierProfile : ContDiff ℝ (⊤ : ℕ∞) (mollifierProfile m) :=
  CKN.mollifier_contDiff one_pos

theorem differentiable_mollifierProfile : Differentiable ℝ (mollifierProfile m) :=
  (contDiff_mollifierProfile (m := m)).differentiable (by simp)

theorem integral_mollifierProfile : ∫ x : Vec m, mollifierProfile m x = 1 :=
  CKN.mollifier_integral_one one_pos

theorem hasCompactSupport_mollifierProfile : HasCompactSupport (mollifierProfile m) :=
  CKN.mollifier_hasCompactSupport one_pos

/-- The profile is supported in the unit ball. -/
theorem support_mollifierProfile :
    Function.support (mollifierProfile m) = Metric.ball (0 : Vec m) 1 := by
  simpa [mollifierProfile, CKN.mollifier, CKN.standardMollifier] using
    (CKN.standardMollifier (d := m) 1 one_pos).support_normed_eq (μ := volume)

theorem mollifierProfile_eq_zero {x : Vec m} (hx : 1 ≤ ‖x‖) : mollifierProfile m x = 0 := by
  by_contra h
  have hmem : x ∈ Function.support (mollifierProfile m) := h
  rw [support_mollifierProfile] at hmem
  have : ‖x‖ < 1 := by simpa using hmem
  exact absurd hx (not_le.mpr this)

/-! ### The rescaled family -/

/-- The rescaled kernel `η_ε(x) = ε^{-m} η(x/ε)`. -/
@[expose] def mollifierKernel (m : ℕ) (ε : ℝ) : Vec m → ℝ :=
  fun x => (ε ^ m)⁻¹ * mollifierProfile m (ε⁻¹ • x)

theorem mollifierKernel_nonneg {ε : ℝ} (hε : 0 < ε) (x : Vec m) :
    0 ≤ mollifierKernel m ε x :=
  mul_nonneg (by positivity) (mollifierProfile_nonneg _)

theorem contDiff_mollifierKernel (ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (mollifierKernel m ε) :=
  contDiff_const.mul (contDiff_mollifierProfile.comp (contDiff_id.const_smul ε⁻¹))

theorem differentiable_mollifierKernel (ε : ℝ) : Differentiable ℝ (mollifierKernel m ε) :=
  (contDiff_mollifierKernel (m := m) ε).differentiable (by simp)

/-- The kernel `η_ε` vanishes outside the ball of radius `ε`. -/
theorem mollifierKernel_eq_zero {ε : ℝ} (hε : 0 < ε) {x : Vec m} (hx : ε ≤ ‖x‖) :
    mollifierKernel m ε x = 0 := by
  have hnorm : 1 ≤ ‖ε⁻¹ • x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε)]
    rw [← inv_mul_cancel₀ (ne_of_gt hε)]
    exact mul_le_mul_of_nonneg_left hx (le_of_lt (inv_pos.mpr hε))
  rw [mollifierKernel, mollifierProfile_eq_zero hnorm, mul_zero]

theorem hasCompactSupport_mollifierKernel {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (mollifierKernel m ε) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Vec m) ε) fun x hx => ?_
  refine mollifierKernel_eq_zero hε ?_
  simpa [Metric.mem_closedBall, dist_zero_right] using le_of_not_ge fun h => hx (by
    simpa [Metric.mem_closedBall, dist_zero_right] using h)

theorem integrable_mollifierKernel {ε : ℝ} (hε : 0 < ε) :
    Integrable (mollifierKernel m ε) volume :=
  (contDiff_mollifierKernel (m := m) ε).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_mollifierKernel hε)

/-- The kernel `η_ε` has unit mass. -/
theorem integral_mollifierKernel {ε : ℝ} (hε : 0 < ε) :
    ∫ x : Vec m, mollifierKernel m ε x = 1 := by
  have hrank : Module.finrank ℝ (Vec m) = m := Module.finrank_fin_fun ℝ
  have hcomp := Measure.integral_comp_smul (μ := (volume : Measure (Vec m)))
    (mollifierProfile m) ε⁻¹
  rw [hrank, inv_pow, inv_inv, integral_mollifierProfile, smul_eq_mul, mul_one,
    abs_of_pos (pow_pos hε m)] at hcomp
  have hne : (ε : ℝ) ^ m ≠ 0 := ne_of_gt (pow_pos hε m)
  calc ∫ x : Vec m, mollifierKernel m ε x
      = (ε ^ m)⁻¹ * ∫ x : Vec m, mollifierProfile m (ε⁻¹ • x) := by
        simp only [mollifierKernel]
        rw [integral_const_mul]
    _ = 1 := by rw [hcomp, inv_mul_cancel₀ hne]

/-! ### The gradient of the kernel -/

/-- The gradient constant `C_η = ∫ ∑_i |∂_iη|` of the fixed profile. -/
@[expose] def mollifierGradConst (m : ℕ) : ℝ :=
  ∫ x : Vec m, ∑ i, |fderiv ℝ (mollifierProfile m) x (basisVec i)|

theorem mollifierGradConst_nonneg : 0 ≤ mollifierGradConst m :=
  integral_nonneg fun _x => Finset.sum_nonneg fun _i _ => abs_nonneg _

theorem fderiv_mollifierKernel_apply (ε : ℝ) (x v : Vec m) :
    fderiv ℝ (mollifierKernel m ε) x v
      = (ε ^ m)⁻¹ * (ε⁻¹ * fderiv ℝ (mollifierProfile m) (ε⁻¹ • x) v) := by
  have hL : HasFDerivAt (fun y : Vec m => ε⁻¹ • y)
      (ε⁻¹ • ContinuousLinearMap.id ℝ (Vec m)) x := (hasFDerivAt_id x).const_smul ε⁻¹
  have hcomp : HasFDerivAt (fun y : Vec m => mollifierProfile m (ε⁻¹ • y))
      ((fderiv ℝ (mollifierProfile m) (ε⁻¹ • x)).comp
        (ε⁻¹ • ContinuousLinearMap.id ℝ (Vec m))) x :=
    HasFDerivAt.comp x (differentiable_mollifierProfile (ε⁻¹ • x)).hasFDerivAt hL
  have h : HasFDerivAt (mollifierKernel m ε)
      ((ε ^ m)⁻¹ • (fderiv ℝ (mollifierProfile m) (ε⁻¹ • x)).comp
        (ε⁻¹ • ContinuousLinearMap.id ℝ (Vec m))) x := hcomp.const_mul ((ε ^ m)⁻¹)
  rw [h.fderiv]
  simp only [smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, map_smul]

/-- The scaling of the gradient integral: `∫ |∇η_ε| = C_η/ε`. -/
theorem integral_sum_abs_fderiv_mollifierKernel {ε : ℝ} (hε : 0 < ε) :
    ∫ x : Vec m, ∑ i, |fderiv ℝ (mollifierKernel m ε) x (basisVec i)|
      = mollifierGradConst m / ε := by
  have hrank : Module.finrank ℝ (Vec m) = m := Module.finrank_fin_fun ℝ
  have hne : (ε : ℝ) ^ m ≠ 0 := ne_of_gt (pow_pos hε m)
  have hpt : ∀ x : Vec m, ∑ i, |fderiv ℝ (mollifierKernel m ε) x (basisVec i)|
      = (ε ^ m)⁻¹ * ε⁻¹ * ∑ i, |fderiv ℝ (mollifierProfile m) (ε⁻¹ • x) (basisVec i)| := by
    intro x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fderiv_mollifierKernel_apply, abs_mul, abs_mul,
      abs_of_pos (inv_pos.mpr (pow_pos hε m)), abs_of_pos (inv_pos.mpr hε), mul_assoc]
  have hcomp := Measure.integral_comp_smul (μ := (volume : Measure (Vec m)))
    (fun y : Vec m => ∑ i, |fderiv ℝ (mollifierProfile m) y (basisVec i)|) ε⁻¹
  rw [hrank, inv_pow, inv_inv, smul_eq_mul, abs_of_pos (pow_pos hε m)] at hcomp
  calc ∫ x : Vec m, ∑ i, |fderiv ℝ (mollifierKernel m ε) x (basisVec i)|
      = ∫ x : Vec m, (ε ^ m)⁻¹ * ε⁻¹ *
          ∑ i, |fderiv ℝ (mollifierProfile m) (ε⁻¹ • x) (basisVec i)| := by
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (ε ^ m)⁻¹ * ε⁻¹ * ∫ x : Vec m,
          ∑ i, |fderiv ℝ (mollifierProfile m) (ε⁻¹ • x) (basisVec i)| := by
        rw [integral_const_mul]
    _ = (ε ^ m)⁻¹ * ε⁻¹ * (ε ^ m * mollifierGradConst m) := by rw [hcomp, mollifierGradConst]
    _ = mollifierGradConst m / ε := by
        field_simp

/-- The gradient of `η_ε` vanishes outside the ball of radius `ε`. -/
theorem fderiv_mollifierKernel_eq_zero {ε : ℝ} (hε : 0 < ε) {w : Vec m} (hw : ε < ‖w‖)
    (v : Vec m) : fderiv ℝ (mollifierKernel m ε) w v = 0 := by
  have hopen : IsOpen {z : Vec m | ε < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hev : mollifierKernel m ε =ᶠ[nhds w] fun _ : Vec m => (0 : ℝ) :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds hw) fun z hz =>
      mollifierKernel_eq_zero hε (le_of_lt hz)
  rw [hev.fderiv_eq]
  simp

theorem continuous_fderiv_mollifierKernel (ε : ℝ) (v : Vec m) :
    Continuous fun w : Vec m => fderiv ℝ (mollifierKernel m ε) w v :=
  (ContinuousLinearMap.apply ℝ ℝ v).continuous.comp
    ((contDiff_mollifierKernel (m := m) ε).continuous_fderiv (by simp))

theorem hasCompactSupport_fderiv_mollifierKernel {ε : ℝ} (hε : 0 < ε) (v : Vec m) :
    HasCompactSupport fun w : Vec m => fderiv ℝ (mollifierKernel m ε) w v := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Vec m) ε) fun w hw => ?_
  refine fderiv_mollifierKernel_eq_zero hε ?_ v
  by_contra hcon
  exact hw (by simpa [Metric.mem_closedBall, dist_zero_right] using not_lt.mp hcon)

theorem integrable_sum_abs_fderiv_mollifierKernel {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun w : Vec m => ∑ i, |fderiv ℝ (mollifierKernel m ε) w (basisVec i)|)
      volume := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact continuous_finsetSum _ fun i _ =>
      (continuous_fderiv_mollifierKernel ε (basisVec i)).abs
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : Vec m) ε) fun w hw => ?_
    refine Finset.sum_eq_zero fun i _ => ?_
    have hzero : fderiv ℝ (mollifierKernel m ε) w (basisVec i) = 0 := by
      refine fderiv_mollifierKernel_eq_zero hε ?_ (basisVec i)
      by_contra hcon
      exact hw (by simpa [Metric.mem_closedBall, dist_zero_right] using not_lt.mp hcon)
    rw [hzero, abs_zero]

end CIV
