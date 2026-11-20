/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Local.ParameterizedHelicalProfile
public import LeanPool.FastDynamo.Analysis.WholePlaneL4FormPerturbationHolder
public import LeanPool.FastDynamo.Local.HorizontalModeWeakIdentity

/-!
# The smoothed velocity `v_h` at a free angular speed, and its `L⁴` distance to `V⁰`

§2.3 of the paper fixes, for `0 < h < 1/2`, a smooth radial cutoff `χ_h`
equal to one on `[0, 1-h]` and zero on `[1+h, ∞)`, and sets

`v_h(y) = χ_h(|y|)(-Ω y₂, Ω y₁, U)`,   `U = -Ω/N`   (`eq:smooth-local-velocity`),

to be compared with the discontinuous screw flow
`V⁰ = 1_{r ≤ 1}(Ω r e_θ + U e₃)` of `eq:jump-flow` (the paper writes `1_{r<1}`; the two agree
almost everywhere).  The proof of `prop:local-seed` uses only that the velocity difference is
uniformly bounded and supported in an annulus of area `O(h)`, whence

`‖v_h - V⁰‖_{L⁴(ℝ²;ℂ³)} ≤ C h^{1/4}`.

The cutoff, the profile and the Schwartz field are already built at a **free** pair of speeds
by `Local/ParameterizedRadialSmoothing.lean` and `Local/ParameterizedHelicalProfile.lean`
(`parameterizedSmoothedVelocity h Ω U`, with the `HelicalProfile` witness
`parameterizedSmoothedHelicalProfile`); the widths are `0 < h < 1`, which contains the paper's
range.  This module makes the comparison against the free-`Ω` jump flow
`horizontalJumpVelocity Ω U` of `Local/HorizontalModeWeakIdentity.lean` (in
`prop:local-seed`, `Ω = -2/Im 𝒟(κ)` is an output of `lem:jump-horizontal-mode`), proves the
`L∞` bound, the support statement and the reality of the error, and packages the error as an
element of `L⁴(ℝ²;ℂ³)` with the rate `O(h^{1/4})`.

Everything here is at the level of velocity coefficients; no form and no spectral statement
occurs.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal SchwartzMap

namespace HorizontalMode

open PonomarenkoFreeOmegaInterface

/-! ## The smoothed velocity and its `L∞` class -/

/-- The `L∞` coefficient of the smoothed velocity `v_h` of `eq:smooth-local-velocity`, at a
free angular speed `Ω` and free axial speed `U`. -/
def horizontalSmoothedVelocityLInf (Omega U : ℝ) (h : PonomarenkoSmoothingWidth) :
    WholePlaneC3LInf :=
  (parameterizedSmoothedVelocity h Omega U).toLp ∞ volume

/-- The smoothed velocity coefficient of the certified mode, with the paper's
`U = -Ω/N`; it is the smoothed counterpart of `horizontalModeVelocity N Ω`. -/
def horizontalSmoothedModeVelocity (N Omega : ℝ) (h : PonomarenkoSmoothingWidth) :
    WholePlaneC3LInf :=
  horizontalSmoothedVelocityLInf Omega (jumpAxialSpeed N Omega) h

/-- The `L∞` class of the smoothed velocity has the Schwartz field as a representative. -/
theorem horizontalSmoothedVelocityLInf_coe_ae (Omega U : ℝ)
    (h : PonomarenkoSmoothingWidth) :
    (horizontalSmoothedVelocityLInf Omega U h : WholePlane → C3) =ᵐ[volume]
      fun y => parameterizedSmoothedVelocity h Omega U y :=
  SchwartzMap.coeFn_toLp _ _ _

/-- The smoothed velocity is the scalar cutoff times the interior screw value
`(-Ω y₂, Ω y₁, U)`. -/
theorem parameterizedSmoothedVelocity_eq_cutoff_smul (Omega U : ℝ)
    (h : PonomarenkoSmoothingWidth) (y : WholePlane) :
    parameterizedSmoothedVelocity h Omega U y =
      (parameterizedRadialCutoff h y : ℂ) • horizontalJumpInteriorVelocity Omega U y := by
  apply PiLp.ext
  intro i
  fin_cases i
  · simp [parameterizedSmoothedVelocity, parameterizedRadialProfile,
      horizontalJumpInteriorVelocity]
    ring
  · simp [parameterizedSmoothedVelocity, parameterizedRadialProfile,
      horizontalJumpInteriorVelocity]
    ring
  · simp [parameterizedSmoothedVelocity, parameterizedRadialProfile,
      horizontalJumpInteriorVelocity]
    ring

/-! ## Agreement with the jump flow off the transition annulus -/

/-- On the plateau `‖y‖ ≤ 1 - h` the smoothed velocity is the jump flow. -/
theorem parameterizedSmoothedVelocity_eq_jump_of_norm_le (Omega U : ℝ)
    (h : PonomarenkoSmoothingWidth) {y : WholePlane} (hy : ‖y‖ ≤ 1 - (h : ℝ)) :
    parameterizedSmoothedVelocity h Omega U y = horizontalJumpVelocity Omega U y := by
  rw [parameterizedSmoothedVelocity_eq_cutoff_smul,
    parameterizedRadialCutoff_one_of_norm_le h hy]
  simp only [Complex.ofReal_one, one_smul]
  exact (horizontalJumpVelocity_of_norm_le Omega U (hy.trans (by linarith [h.2.1]))).symm

/-- Outside the ball of radius `1 + h` the smoothed velocity and the jump flow both vanish. -/
theorem parameterizedSmoothedVelocity_eq_jump_of_radius_le_norm (Omega U : ℝ)
    (h : PonomarenkoSmoothingWidth) {y : WholePlane} (hy : 1 + (h : ℝ) ≤ ‖y‖) :
    parameterizedSmoothedVelocity h Omega U y = horizontalJumpVelocity Omega U y := by
  rw [parameterizedSmoothedVelocity_eq_cutoff_smul,
    parameterizedRadialCutoff_zero_of_radius_le_norm h hy]
  simp only [Complex.ofReal_zero, zero_smul]
  exact (horizontalJumpVelocity_of_one_lt_norm Omega U (by linarith [h.2.1])).symm

/-- Off the open transition annulus `1 - h < ‖y‖ < 1 + h` the two velocities agree, so the
whole smoothing error lives in that annulus (proof of `prop:local-seed`). -/
theorem parameterizedSmoothedVelocity_eq_jump_off_annulus (Omega U : ℝ)
    (h : PonomarenkoSmoothingWidth) {y : WholePlane}
    (hy : y ∉ ponomarenkoSmoothingAnnulus h) :
    parameterizedSmoothedVelocity h Omega U y = horizontalJumpVelocity Omega U y := by
  change ¬(1 - (h : ℝ) < ‖y‖ ∧ ‖y‖ < 1 + (h : ℝ)) at hy
  rw [not_and_or] at hy
  rcases hy with hy | hy
  · exact parameterizedSmoothedVelocity_eq_jump_of_norm_le Omega U h (le_of_not_gt hy)
  · exact parameterizedSmoothedVelocity_eq_jump_of_radius_le_norm Omega U h (le_of_not_gt hy)

/-! ## Pointwise and uniform bounds -/

/-- The smoothed velocity is pointwise dominated by the unrestricted interior screw value,
the cutoff taking values in `[0,1]`. -/
theorem norm_parameterizedSmoothedVelocity_le_interior (Omega U : ℝ)
    (h : PonomarenkoSmoothingWidth) (y : WholePlane) :
    ‖parameterizedSmoothedVelocity h Omega U y‖ ≤
      ‖horizontalJumpInteriorVelocity Omega U y‖ := by
  rw [parameterizedSmoothedVelocity_eq_cutoff_smul, norm_smul]
  have hc := parameterizedRadialCutoff_mem_Icc h y
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hc.2

/-- The jump flow is pointwise dominated by the unrestricted interior screw value. -/
theorem norm_horizontalJumpVelocity_le_interior (Omega U : ℝ) (y : WholePlane) :
    ‖horizontalJumpVelocity Omega U y‖ ≤ ‖horizontalJumpInteriorVelocity Omega U y‖ := by
  by_cases hy : ‖y‖ ≤ 1
  · rw [horizontalJumpVelocity_of_norm_le Omega U hy]
  · rw [horizontalJumpVelocity_of_one_lt_norm Omega U (lt_of_not_ge hy), norm_zero]
    exact norm_nonneg _

/-- A uniform pointwise majorant for the smoothing error. -/
theorem norm_parameterizedSmoothedVelocity_sub_jump_le (Omega U : ℝ)
    (h : PonomarenkoSmoothingWidth) (y : WholePlane) :
    ‖parameterizedSmoothedVelocity h Omega U y - horizontalJumpVelocity Omega U y‖ ≤
      2 * ‖horizontalJumpInteriorVelocity Omega U y‖ := by
  calc
    ‖parameterizedSmoothedVelocity h Omega U y - horizontalJumpVelocity Omega U y‖ ≤
        ‖parameterizedSmoothedVelocity h Omega U y‖ +
          ‖horizontalJumpVelocity Omega U y‖ := norm_sub_le _ _
    _ ≤ ‖horizontalJumpInteriorVelocity Omega U y‖ +
          ‖horizontalJumpInteriorVelocity Omega U y‖ :=
      add_le_add (norm_parameterizedSmoothedVelocity_le_interior Omega U h y)
        (norm_horizontalJumpVelocity_le_interior Omega U y)
    _ = 2 * ‖horizontalJumpInteriorVelocity Omega U y‖ := by ring

/-- The interior screw value is bounded on the disc of radius two; this one bound serves the
whole family of widths. -/
theorem exists_nonneg_horizontalJumpInteriorVelocity_bound_two (Omega U : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : WholePlane, ‖y‖ ≤ 2 →
      ‖horizontalJumpInteriorVelocity Omega U y‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : WholePlane) 2).bddAbove_image
    (horizontalJumpInteriorVelocity_continuous Omega U).norm.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun y hy => ?_⟩
  have hymem : y ∈ closedBall (0 : WholePlane) 2 := by
    simpa [mem_closedBall, dist_zero_right] using hy
  exact (hC (mem_image_of_mem _ hymem)).trans (le_max_left _ _)

/-! ## Reality of the velocities and of the smoothing error -/

/-- The interior screw value has real components. -/
theorem horizontalJumpInteriorVelocity_im (Omega U : ℝ) (y : WholePlane) (i : Fin 3) :
    (horizontalJumpInteriorVelocity Omega U y i).im = 0 := by
  fin_cases i <;>
    simp [horizontalJumpInteriorVelocity, Complex.mul_im]

/-- The jump flow has real components. -/
theorem horizontalJumpVelocity_im (Omega U : ℝ) (y : WholePlane) (i : Fin 3) :
    (horizontalJumpVelocity Omega U y i).im = 0 := by
  by_cases hy : ‖y‖ ≤ 1
  · rw [horizontalJumpVelocity_of_norm_le Omega U hy]
    exact horizontalJumpInteriorVelocity_im Omega U y i
  · rw [horizontalJumpVelocity_of_one_lt_norm Omega U (lt_of_not_ge hy)]
    simp

/-- The smoothed velocity has real components. -/
theorem parameterizedSmoothedVelocity_im (Omega U : ℝ) (h : PonomarenkoSmoothingWidth)
    (y : WholePlane) (i : Fin 3) :
    (parameterizedSmoothedVelocity h Omega U y i).im = 0 := by
  rw [parameterizedSmoothedVelocity_eq_cutoff_smul]
  have hcoord : ((parameterizedRadialCutoff h y : ℂ) •
      horizontalJumpInteriorVelocity Omega U y) i =
      (parameterizedRadialCutoff h y : ℂ) * horizontalJumpInteriorVelocity Omega U y i := by
    simp
  rw [hcoord, Complex.mul_im, horizontalJumpInteriorVelocity_im]
  simp

/-- The smoothing error has real components: this is the paper's real velocity field, and
it is what lets the transport and stretching terms be estimated with the coefficient moved onto
the test function. -/
theorem parameterizedSmoothedVelocity_sub_jump_im (Omega U : ℝ)
    (h : PonomarenkoSmoothingWidth) (y : WholePlane) (i : Fin 3) :
    ((parameterizedSmoothedVelocity h Omega U y - horizontalJumpVelocity Omega U y) i).im
      = 0 := by
  have hsub : (parameterizedSmoothedVelocity h Omega U y -
      horizontalJumpVelocity Omega U y) i =
      parameterizedSmoothedVelocity h Omega U y i - horizontalJumpVelocity Omega U y i := by
    simp
  rw [hsub, Complex.sub_im, parameterizedSmoothedVelocity_im, horizontalJumpVelocity_im]
  ring

/-! ## The `L⁴` smoothing error -/

/-- The smoothing error is supported in the closed transition annulus. -/
private theorem horizontalSmoothing_error_indicator (Omega U : ℝ)
    (h : PonomarenkoSmoothingWidth) :
    (ponomarenkoSmoothingClosedAnnulus h).indicator
        ((fun y : WholePlane => parameterizedSmoothedVelocity h Omega U y) -
          horizontalJumpVelocity Omega U) =
      (fun y : WholePlane => parameterizedSmoothedVelocity h Omega U y) -
        horizontalJumpVelocity Omega U := by
  funext y
  by_cases hy : y ∈ ponomarenkoSmoothingClosedAnnulus h
  · rw [Set.indicator_of_mem hy]
  · rw [Set.indicator_of_notMem hy]
    have hopen : y ∉ ponomarenkoSmoothingAnnulus h := by
      intro hopen
      apply hy
      refine ⟨?_, ?_⟩
      · simpa [mem_closedBall, dist_zero_right] using hopen.2.le
      · simpa [mem_ball, dist_zero_right, not_lt] using hopen.1.le
    change (0 : C3) =
      parameterizedSmoothedVelocity h Omega U y - horizontalJumpVelocity Omega U y
    rw [parameterizedSmoothedVelocity_eq_jump_off_annulus Omega U h hopen]
    simp

/-- Quantitative annular `L⁴` estimate for the smoothing error: the right-hand side is
`2C(4πh)^{1/4}` for any radius-two bound `C` of the interior screw value
(proof of `prop:local-seed`). -/
theorem eLpNorm_four_parameterizedSmoothedVelocity_sub_jump_le (Omega U : ℝ)
    (h : PonomarenkoSmoothingWidth) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ y : WholePlane, ‖y‖ ≤ 2 →
      ‖horizontalJumpInteriorVelocity Omega U y‖ ≤ C) :
    eLpNorm (fun y : WholePlane =>
        parameterizedSmoothedVelocity h Omega U y - horizontalJumpVelocity Omega U y)
        (4 : ℝ≥0∞) volume ≤
      ENNReal.ofReal (2 * C) * ENNReal.ofReal (4 * Real.pi * (h : ℝ)) ^ (1 / 4 : ℝ) := by
  rw [← volume_ponomarenkoSmoothingClosedAnnulus h]
  change eLpNorm ((fun y : WholePlane => parameterizedSmoothedVelocity h Omega U y) -
    horizontalJumpVelocity Omega U) (4 : ℝ≥0∞) volume ≤ _
  rw [← horizontalSmoothing_error_indicator Omega U h]
  apply eLpNorm_indicator_sub_le_of_dist_bdd volume (p := (4 : ℝ≥0∞)) (by norm_num)
    (measurableSet_ponomarenkoSmoothingClosedAnnulus h).nullMeasurableSet
    (mul_nonneg (by norm_num) hC)
    ((((parameterizedSmoothedVelocity h Omega U).continuous.stronglyMeasurable.sub
      (horizontalJumpVelocity_stronglyMeasurable Omega U)).indicator
      (measurableSet_ponomarenkoSmoothingClosedAnnulus h)).aestronglyMeasurable)
  intro y hy
  rw [dist_eq_norm]
  refine (norm_parameterizedSmoothedVelocity_sub_jump_le Omega U h y).trans ?_
  apply mul_le_mul_of_nonneg_left
  · apply hbound
    have hyouter : ‖y‖ ≤ 1 + (h : ℝ) := by
      simpa [ponomarenkoSmoothingClosedAnnulus, mem_closedBall, dist_zero_right] using hy.1
    linarith [h.2.2]
  · norm_num

/-- The pointwise smoothing error belongs to `L⁴(ℝ²;ℂ³)`. -/
theorem parameterizedSmoothedVelocity_sub_jump_memLp_four (Omega U : ℝ)
    (h : PonomarenkoSmoothingWidth) :
    MemLp (fun y : WholePlane =>
      parameterizedSmoothedVelocity h Omega U y - horizontalJumpVelocity Omega U y)
      (4 : ℝ≥0∞) volume := by
  obtain ⟨C, hC, hbound⟩ := exists_nonneg_horizontalJumpInteriorVelocity_bound_two Omega U
  rw [memLp_iff]
  refine (eLpNorm_four_parameterizedSmoothedVelocity_sub_jump_le Omega U h hC
    hbound).trans_lt ?_
  finiteness

/-- The velocity difference `v_h - V⁰` as an element of `L⁴(ℝ²;ℂ³)`; this is the object whose
norm carries the `h^{1/4}` rate of `eq:form-small`. -/
def horizontalSmoothingErrorL4 (Omega U : ℝ) (h : PonomarenkoSmoothingWidth) :
    WholePlaneC3L4 :=
  (parameterizedSmoothedVelocity_sub_jump_memLp_four Omega U h).toLp
    (fun y : WholePlane =>
      parameterizedSmoothedVelocity h Omega U y - horizontalJumpVelocity Omega U y)

/-- The bundled `L⁴` error has the expected pointwise representative. -/
theorem horizontalSmoothingErrorL4_coe_ae (Omega U : ℝ) (h : PonomarenkoSmoothingWidth) :
    (horizontalSmoothingErrorL4 Omega U h : WholePlane → C3) =ᵐ[volume]
      fun y => parameterizedSmoothedVelocity h Omega U y - horizontalJumpVelocity Omega U y :=
  MemLp.coeFn_toLp _

/-- The bundled `L⁴` error is almost everywhere the difference of the two `L∞` coefficients. -/
theorem horizontalSmoothingErrorL4_coe_ae_sub (Omega U : ℝ)
    (h : PonomarenkoSmoothingWidth) :
    (horizontalSmoothingErrorL4 Omega U h : WholePlane → C3) =ᵐ[volume]
      fun y => (horizontalSmoothedVelocityLInf Omega U h : WholePlane → C3) y -
        (horizontalJumpVelocityLInf Omega U : WholePlane → C3) y := by
  filter_upwards [horizontalSmoothingErrorL4_coe_ae Omega U h,
    horizontalSmoothedVelocityLInf_coe_ae Omega U h,
    horizontalJumpVelocityLInf_coe_ae Omega U] with y h4 hs hj
  rw [h4, hs, hj]

/-- The bundled `L⁴` error has real components. -/
theorem horizontalSmoothingErrorL4_im (Omega U : ℝ) (h : PonomarenkoSmoothingWidth) :
    ∀ᵐ y ∂volume, ∀ i : Fin 3,
      ((horizontalSmoothingErrorL4 Omega U h : WholePlane → C3) y i).im = 0 := by
  filter_upwards [horizontalSmoothingErrorL4_coe_ae Omega U h] with y hy i
  rw [hy]
  exact parameterizedSmoothedVelocity_sub_jump_im Omega U h y i

/-- The quotient-level `L⁴` rate `‖v_h - V⁰‖₄ ≤ 2C(4πh)^{1/4}`. -/
theorem norm_horizontalSmoothingErrorL4_le (Omega U : ℝ) (h : PonomarenkoSmoothingWidth)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ y : WholePlane, ‖y‖ ≤ 2 →
      ‖horizontalJumpInteriorVelocity Omega U y‖ ≤ C) :
    ‖horizontalSmoothingErrorL4 Omega U h‖ ≤
      ENNReal.toReal (ENNReal.ofReal (2 * C) *
        ENNReal.ofReal (4 * Real.pi * (h : ℝ)) ^ (1 / 4 : ℝ)) := by
  rw [horizontalSmoothingErrorL4, Lp.norm_toLp]
  refine ENNReal.toReal_mono (by finiteness) ?_
  exact eLpNorm_four_parameterizedSmoothedVelocity_sub_jump_le Omega U h hC hbound

/-- **The `h^{1/4}` rate of `eq:form-small`**, fully discharged: for fixed speeds there is one
constant `C₀ ≥ 0` with
`‖v_h - V⁰‖_{L⁴(ℝ²;ℂ³)} ≤ C₀ h^{1/4}` for every smoothing width `h`. -/
theorem exists_norm_horizontalSmoothingErrorL4_le (Omega U : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : PonomarenkoSmoothingWidth,
      ‖horizontalSmoothingErrorL4 Omega U h‖ ≤ C * (h : ℝ) ^ (1 / 4 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := exists_nonneg_horizontalJumpInteriorVelocity_bound_two Omega U
  refine ⟨2 * C * (4 * Real.pi) ^ (1 / 4 : ℝ), by positivity, fun h => ?_⟩
  refine (norm_horizontalSmoothingErrorL4_le Omega U h hC hbound).trans_eq ?_
  have hh : (0 : ℝ) ≤ (h : ℝ) := h.2.1.le
  have hpi : (0 : ℝ) ≤ 4 * Real.pi := by positivity
  have hrw : (ENNReal.ofReal (4 * Real.pi * (h : ℝ)) ^ (1 / 4 : ℝ)).toReal =
      (4 * Real.pi * (h : ℝ)) ^ (1 / 4 : ℝ) := by
    rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (by positivity)]
  rw [ENNReal.toReal_mul, hrw, ENNReal.toReal_ofReal (by positivity),
    Real.mul_rpow hpi hh]
  ring

end HorizontalMode

end

end FastDynamo
