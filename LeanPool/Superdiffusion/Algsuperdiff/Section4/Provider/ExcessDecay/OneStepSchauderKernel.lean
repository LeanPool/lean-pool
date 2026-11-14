/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# OneStepSchauderKernel

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The native unit-mass radial mollifier

The interior Schauder estimate is proved by the
*reproducing-convolution* route: a harmonic function reproduces itself against
any unit-mass radial kernel, and derivatives are then moved onto the **kernel**,
where they are bounded by an explicit dimensional constant.  This module builds
that kernel:

* `radialProfile` — the scalar profile `s ↦ smoothTransition (1 - s)`;
* `radialKernelAux d` — `x ↦ radialProfile ‖x‖²`, smooth, nonnegative, radial,
  supported in the closed unit ball, positive at the origin;
* `radialKernel d` — the same divided by its (strictly positive) mass, so
  `∫ radialKernel d = 1`;
* `radialKernelScaled d ε` — the `ε`-dilate `z ↦ (ε^d)⁻¹ · radialKernel d (ε⁻¹ • z)`,
  supported in `closedBall 0 ε`, again of unit mass.
-/

-- ==== the kernel ====
open scoped Real
open MeasureTheory Metric

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

/-! ### The scalar radial profile -/

/-- The scalar radial profile `s ↦ smoothTransition (1 - s)`: `C^∞`, nonnegative,
`= 1` for `s ≤ 0`, positive for `s < 1`, and `= 0` for `1 ≤ s`.  Composed with
the squared norm it yields a smooth radial bump supported in the unit ball.
(Port of K `radialSqProfile`, mathlib-native.) -/
def radialProfile (s : ℝ) : ℝ := Real.smoothTransition (1 - s)

theorem radialProfile_contDiff {n : ℕ∞} : ContDiff ℝ n radialProfile :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem radialProfile_nonneg (s : ℝ) : 0 ≤ radialProfile s :=
  Real.smoothTransition.nonneg _

theorem radialProfile_eq_zero_of_one_le {s : ℝ} (hs : 1 ≤ s) : radialProfile s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

@[simp] theorem radialProfile_zero : radialProfile 0 = 1 := by
  simp [radialProfile, Real.smoothTransition.one_of_one_le]

/-! ### The un-normalized radial kernel -/

variable (d : ℕ)

/-- The un-normalized native radial mollifier on `EuclideanSpace ℝ (Fin d)`:
`x ↦ radialProfile (‖x‖²)`.  Smooth, nonnegative, radial, supported in the closed unit ball, and
positive at the origin. -/
def radialKernelAux : EuclideanSpace ℝ (Fin d) → ℝ := fun x => radialProfile (‖x‖ ^ 2)

theorem radialKernelAux_contDiff {n : ℕ∞} : ContDiff ℝ n (radialKernelAux d) :=
  radialProfile_contDiff.comp (contDiff_norm_sq ℝ)

theorem radialKernelAux_nonneg (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ radialKernelAux d x :=
  radialProfile_nonneg _

/-- **Radiality.**  The un-normalized kernel depends on `x` only through `‖x‖`. -/
theorem radialKernelAux_radial {x y : EuclideanSpace ℝ (Fin d)} (h : ‖x‖ = ‖y‖) :
    radialKernelAux d x = radialKernelAux d y := by
  simp only [radialKernelAux, h]

theorem radialKernelAux_eq_zero_of_one_le_norm {x : EuclideanSpace ℝ (Fin d)} (hx : 1 ≤ ‖x‖) :
    radialKernelAux d x = 0 :=
  radialProfile_eq_zero_of_one_le (by nlinarith [norm_nonneg x])

@[simp] theorem radialKernelAux_zero : radialKernelAux d 0 = 1 := by
  simp [radialKernelAux]

/-- The support of the un-normalized kernel is contained in the closed unit ball. -/
theorem support_radialKernelAux_subset :
    Function.support (radialKernelAux d) ⊆ closedBall 0 1 := by
  intro x hx
  rw [Function.mem_support] at hx
  rw [mem_closedBall, dist_zero_right]
  by_contra h
  exact hx (radialKernelAux_eq_zero_of_one_le_norm d (le_of_lt (not_le.mp h)))

theorem tsupport_radialKernelAux_subset :
    tsupport (radialKernelAux d) ⊆ closedBall 0 1 :=
  closure_minimal (support_radialKernelAux_subset d) isClosed_closedBall

theorem radialKernelAux_hasCompactSupport : HasCompactSupport (radialKernelAux d) :=
  (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).of_isClosed_subset isClosed_closure
    (tsupport_radialKernelAux_subset d)

theorem radialKernelAux_continuous : Continuous (radialKernelAux d) :=
  (radialKernelAux_contDiff (d := d) (n := 1)).continuous

/-- **Strictly positive mass.**  The un-normalized kernel has a strictly positive integral (it is a
nonnegative continuous compactly-supported function, positive at the origin). -/
theorem radialKernelAux_integral_pos : 0 < ∫ x, radialKernelAux d x ∂volume :=
  (radialKernelAux_continuous d).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (radialKernelAux_hasCompactSupport d) (radialKernelAux_nonneg d)
    (x := 0) (by simp)

theorem radialKernelAux_integral_ne_zero : (∫ x, radialKernelAux d x ∂volume) ≠ 0 :=
  (radialKernelAux_integral_pos d).ne'

/-! ### The unit-mass radial kernel -/

/-- The unit-mass native radial mollifier on `EuclideanSpace ℝ (Fin d)`: the
un-normalized kernel divided by its (strictly positive) total mass.  Smooth,
nonnegative, radial, supported in the closed unit ball, and of total mass `1`.
(Native port of K `normalizedRadialSqProfile`.) -/
def radialKernel : EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x => radialKernelAux d x / ∫ y, radialKernelAux d y ∂volume

theorem radialKernel_contDiff {n : ℕ∞} : ContDiff ℝ n (radialKernel d) :=
  (radialKernelAux_contDiff d).div_const _

/-- **Radiality.**  The unit-mass kernel depends on `x` only through `‖x‖`. -/
theorem radialKernel_radial {x y : EuclideanSpace ℝ (Fin d)} (h : ‖x‖ = ‖y‖) :
    radialKernel d x = radialKernel d y := by
  simp only [radialKernel, radialKernelAux_radial d h]

theorem radialKernel_eq_zero_of_one_le_norm {x : EuclideanSpace ℝ (Fin d)} (hx : 1 ≤ ‖x‖) :
    radialKernel d x = 0 := by
  simp [radialKernel, radialKernelAux_eq_zero_of_one_le_norm d hx]

theorem support_radialKernel_subset :
    Function.support (radialKernel d) ⊆ closedBall 0 1 := by
  intro x hx
  rw [Function.mem_support] at hx
  refine support_radialKernelAux_subset d ?_
  rw [Function.mem_support]
  intro h
  exact hx (by simp [radialKernel, h])

theorem tsupport_radialKernel_subset :
    tsupport (radialKernel d) ⊆ closedBall 0 1 :=
  closure_minimal (support_radialKernel_subset d) isClosed_closedBall

theorem radialKernel_hasCompactSupport : HasCompactSupport (radialKernel d) :=
  (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).of_isClosed_subset isClosed_closure
    (tsupport_radialKernel_subset d)

/-- **Unit mass.**  The normalized kernel integrates to `1`. -/
theorem radialKernel_integral_eq_one : ∫ x, radialKernel d x ∂volume = 1 := by
  simp only [radialKernel]
  rw [integral_div, div_self (radialKernelAux_integral_ne_zero d)]

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

-- ==== the scaled kernel ====
open scoped Real
open MeasureTheory Metric

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable (d : ℕ)

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- The `ε`-scaled native radial mollifier: `K_ε(z) = ε⁻ᵈ · radialKernel d (ε⁻¹ • z)`. -/
def radialKernelScaled (ε : ℝ) : 𝔼 → ℝ :=
  fun z => (ε ^ d)⁻¹ * radialKernel d (ε⁻¹ • z)

theorem radialKernelScaled_apply (ε : ℝ) (z : 𝔼) :
    radialKernelScaled d ε z = (ε ^ d)⁻¹ * radialKernel d (ε⁻¹ • z) := rfl

theorem radialKernelScaled_contDiff {ε : ℝ} {n : ℕ∞} : ContDiff ℝ n (radialKernelScaled d ε) := by
  have hlin : ContDiff ℝ n (fun z : 𝔼 => ε⁻¹ • z) :=
    (contDiff_const_smul (ε⁻¹ : ℝ))
  exact (contDiff_const.mul ((radialKernel_contDiff d).comp hlin))

/-- **Radiality.**  The scaled kernel depends on `z` only through `‖z‖`. -/
theorem radialKernelScaled_radial {ε : ℝ} {a b : 𝔼} (h : ‖a‖ = ‖b‖) :
    radialKernelScaled d ε a = radialKernelScaled d ε b := by
  simp only [radialKernelScaled]
  rw [radialKernel_radial d (show ‖ε⁻¹ • a‖ = ‖ε⁻¹ • b‖ by rw [norm_smul, norm_smul, h])]

/-- The scaled kernel vanishes outside the open ball of radius `ε`. -/
theorem radialKernelScaled_eq_zero_of_le_norm {ε : ℝ} (hε : 0 < ε) {z : 𝔼} (hz : ε ≤ ‖z‖) :
    radialKernelScaled d ε z = 0 := by
  have h1 : 1 ≤ ‖ε⁻¹ • z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hε)]
    rw [inv_mul_eq_div, le_div_iff₀ hε, one_mul]
    exact hz
  simp [radialKernelScaled, radialKernel_eq_zero_of_one_le_norm d h1]

theorem support_radialKernelScaled_subset {ε : ℝ} (hε : 0 < ε) :
    Function.support (radialKernelScaled d ε) ⊆ closedBall 0 ε := by
  intro z hz
  rw [Function.mem_support] at hz
  rw [mem_closedBall, dist_zero_right]
  by_contra h
  exact hz (radialKernelScaled_eq_zero_of_le_norm d hε (le_of_lt (not_le.mp h)))

theorem tsupport_radialKernelScaled_subset {ε : ℝ} (hε : 0 < ε) :
    tsupport (radialKernelScaled d ε) ⊆ closedBall 0 ε :=
  closure_minimal (support_radialKernelScaled_subset d hε) isClosed_closedBall

theorem radialKernelScaled_hasCompactSupport {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (radialKernelScaled d ε) :=
  (isCompact_closedBall (0 : 𝔼) ε).of_isClosed_subset isClosed_closure
    (tsupport_radialKernelScaled_subset d hε)

theorem radialKernelScaled_continuous {ε : ℝ} : Continuous (radialKernelScaled d ε) :=
  (radialKernelScaled_contDiff (d := d) (ε := ε) (n := 1)).continuous

/-- **Unit mass.**  The `ε`-rescaling preserves total mass: `∫ K_ε = 1`.  The dilation Jacobian
`ε⁻ᵈ` exactly cancels the `εᵈ` from the change of variables `z ↦ ε⁻¹ • z`. -/
theorem radialKernelScaled_integral_eq_one {ε : ℝ} (hε : 0 < ε) :
    ∫ z, radialKernelScaled d ε z = 1 := by
  have hfr : Module.finrank ℝ 𝔼 = d := finrank_euclideanSpace_fin
  calc ∫ z, radialKernelScaled d ε z
      = (ε ^ d)⁻¹ * ∫ z, radialKernel d (ε⁻¹ • z) := by
        simp only [radialKernelScaled]; rw [integral_const_mul]
    _ = (ε ^ d)⁻¹ * (ε ^ (Module.finrank ℝ 𝔼) • ∫ z, radialKernel d z) := by
        rw [MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg (volume : Measure 𝔼)
          (radialKernel d) hε.le]
    _ = (ε ^ d)⁻¹ * (ε ^ d • (1 : ℝ)) := by rw [hfr, radialKernel_integral_eq_one]
    _ = 1 := by rw [smul_eq_mul, mul_one]; exact inv_mul_cancel₀ (by positivity)

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

