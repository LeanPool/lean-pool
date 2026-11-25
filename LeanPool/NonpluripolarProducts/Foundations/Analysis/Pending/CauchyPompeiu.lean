/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# The Cauchy–Pompeiu formula for compactly supported functions

For a compactly supported `C¹` function `φ : ℂ → ℂ`,
`∫ (∂φ/∂wBar)(w) / w dA(w) = -π φ(0)`, i.e. `∂bar(1/(π z)) = δ₀` in the sense of
distributions.  The proof uses polar coordinates: after multiplication by the
Jacobian `r`, the integrand splits into a radial derivative and an angular
derivative divided by `r`; the first integrates to `-φ(0)` along every ray and
the second to zero along every circle.
-/

@[expose] public section

open MeasureTheory Set Filter Complex
open scoped Topology Real

namespace SGPT.Foundations.Analysis.Pending.CauchyGreen

noncomputable section

/-- The Wirtinger derivative `∂/∂wBar = (∂/∂x + i ∂/∂y)/2` of a function `ℂ → ℂ`. -/
def dbar (φ : ℂ → ℂ) (w : ℂ) : ℂ :=
  (fderiv ℝ φ w 1 + I * fderiv ℝ φ w I) / 2

/-- The unit complex number of angle `θ`, in the form used by polar coordinates. -/
private def unit (θ : ℝ) : ℂ := (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I

/-- The pointwise polar splitting of `r · (∂φ/∂wBar)(r e^{iθ}) / (r e^{iθ})`. -/
private theorem polar_integrand_eq (L : ℂ →L[ℝ] ℂ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    r • (((r : ℂ) * unit θ)⁻¹ * ((L 1 + I * L I) / 2)) =
      (1 / 2 : ℂ) * (L (unit θ) + I * L (I * unit θ)) := by
  have hu : unit θ = (Real.cos θ : ℝ) • (1 : ℂ) + (Real.sin θ : ℝ) • I := by
    simp [unit, Complex.real_smul]
  have hIu : I * unit θ = (-Real.sin θ : ℝ) • (1 : ℂ) + (Real.cos θ : ℝ) • I := by
    simp only [unit, Complex.real_smul]
    push_cast
    ring_nf
    rw [I_sq]
    ring
  have hinv : (unit θ)⁻¹ = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I := by
    rw [inv_eq_of_mul_eq_one_right]
    simp only [unit]
    ring_nf
    rw [I_sq]
    have := Real.cos_sq_add_sin_sq θ
    have h' : ((Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2) = 1 := by
      exact_mod_cast this
    linear_combination h'
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [Complex.real_smul, mul_inv, hinv, hIu, hu, map_add, map_add, map_smul,
    map_smul, map_smul, map_smul]
  simp only [Complex.real_smul]
  push_cast
  field_simp
  ring_nf
  rw [I_sq]
  ring

private theorem unit_continuous : Continuous unit := by
  unfold unit
  fun_prop

private theorem norm_unit (θ : ℝ) : ‖unit θ‖ = 1 := by
  have h := Complex.norm_polarCoord_symm (1, θ)
  rw [Complex.polarCoord_symm_apply] at h
  simp only [Complex.ofReal_one, one_mul, abs_one] at h
  exact h

private theorem hasDerivAt_ray (θ r : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (s : ℂ) * unit θ) (unit θ) r := by
  simpa using (hasDerivAt_id r).ofReal_comp.mul_const (unit θ)

private theorem hasDerivAt_circle (r θ : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (r : ℂ) * unit s) ((r : ℂ) * (I * unit θ)) θ := by
  have hc := (Real.hasDerivAt_cos θ).ofReal_comp
  have hs := (Real.hasDerivAt_sin θ).ofReal_comp
  have h : HasDerivAt (fun s : ℝ ↦ (r : ℂ) * unit s)
      ((r : ℂ) * (((-Real.sin θ : ℝ) : ℂ) + ((Real.cos θ : ℝ) : ℂ) * I)) θ :=
    (hc.add (hs.mul_const I)).const_mul (r : ℂ)
  convert h using 2
  simp only [unit]
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- A continuous function on `ℝ × ℝ` vanishing for large first coordinate is
integrable on the polar-coordinate target. -/
private theorem integrableOn_target_of_vanishing {G : ℝ × ℝ → ℂ}
    (hG : Continuous G) {M : ℝ} (hM : ∀ p : ℝ × ℝ, M < p.1 → G p = 0) :
    IntegrableOn G (Ioi 0 ×ˢ Ioo (-π) π) := by
  have hbox : IntegrableOn G (Icc 0 M ×ˢ Icc (-π) π) :=
    hG.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  refine hbox.of_forall_sdiff_eq_zero (measurableSet_Ioi.prod measurableSet_Ioo) ?_
  rintro ⟨r, θ⟩ ⟨⟨hr, hθ⟩, hnot⟩
  apply hM
  by_contra hle
  exact hnot ⟨⟨le_of_lt hr, not_lt.mp hle⟩, Ioo_subset_Icc_self hθ⟩

theorem integral_inv_mul_dbar {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) :
    ∫ w : ℂ, w⁻¹ * dbar φ w = -(π : ℂ) * φ 0 := by
  obtain ⟨M, hM⟩ := hc.isCompact.isBounded.subset_closedBall 0
  have hzero : ∀ w : ℂ, M < ‖w‖ → φ w = 0 := fun w hw ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ by
      have := hM h
      rw [Metric.mem_closedBall, dist_zero_right] at this
      linarith
  have hdzero : ∀ w : ℂ, M < ‖w‖ → fderiv ℝ φ w = 0 := fun w hw ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ by
      have := hM (tsupport_fderiv_subset ℝ h)
      rw [Metric.mem_closedBall, dist_zero_right] at this
      linarith
  have hL : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  have hφdiff : ∀ w, HasFDerivAt φ (fderiv ℝ φ w) w := fun w ↦
    ((hφ.differentiable one_ne_zero) w).hasFDerivAt
  let R : ℝ × ℝ → ℂ := fun p ↦ fderiv ℝ φ ((p.1 : ℂ) * unit p.2) (unit p.2)
  let T : ℝ × ℝ → ℂ := fun p ↦ fderiv ℝ φ ((p.1 : ℂ) * unit p.2) (I * unit p.2)
  have hpath : Continuous (fun p : ℝ × ℝ ↦ (p.1 : ℂ) * unit p.2) := by
    have := unit_continuous
    fun_prop
  have hRc : Continuous R :=
    (hL.comp hpath).clm_apply (unit_continuous.comp continuous_snd)
  have hTc : Continuous T :=
    (hL.comp hpath).clm_apply (continuous_const.mul (unit_continuous.comp continuous_snd))
  have hnorm : ∀ p : ℝ × ℝ, M < p.1 → M < ‖(p.1 : ℂ) * unit p.2‖ := by
    intro p hp
    rw [norm_mul, norm_unit, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact lt_of_lt_of_le hp (le_abs_self _)
  have hRv : ∀ p : ℝ × ℝ, M < p.1 → R p = 0 := fun p hp ↦ by
    simp [R, hdzero _ (hnorm p hp)]
  have hTv : ∀ p : ℝ × ℝ, M < p.1 → T p = 0 := fun p hp ↦ by
    simp [T, hdzero _ (hnorm p hp)]
  have hRi := integrableOn_target_of_vanishing hRc hRv
  have hTi := integrableOn_target_of_vanishing hTc hTv
  -- Polar coordinates.
  have hpolar : ∫ w : ℂ, w⁻¹ * dbar φ w =
      ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, (1 / 2 : ℂ) * (R p + I * T p) := by
    rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
    refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) ?_
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    dsimp only
    rw [Complex.polarCoord_symm_apply]
    exact polar_integrand_eq (fderiv ℝ φ ((r : ℂ) * unit θ)) hr θ
  -- The radial derivative integrates to `-φ 0` along each ray.
  have hray : ∀ θ : ℝ, ∫ r in Ioi (0 : ℝ), R (r, θ) = -φ 0 := by
    intro θ
    have hderiv : ∀ r ∈ Ioi (0 : ℝ),
        HasDerivAt (fun s : ℝ ↦ φ ((s : ℂ) * unit θ)) (R (r, θ)) r := fun r _ ↦
      (hφdiff _).comp_hasDerivAt r (hasDerivAt_ray θ r)
    have hcont : Continuous (fun s : ℝ ↦ φ ((s : ℂ) * unit θ)) := by
      have := unit_continuous
      exact hφ.continuous.comp (by fun_prop)
    have hint : IntegrableOn (fun r : ℝ ↦ R (r, θ)) (Ioi 0) := by
      have hbox : IntegrableOn (fun r : ℝ ↦ R (r, θ)) (Icc 0 M) :=
        (hRc.comp (continuous_id.prodMk continuous_const)).continuousOn.integrableOn_compact
          isCompact_Icc
      refine hbox.of_forall_sdiff_eq_zero measurableSet_Ioi ?_
      rintro r ⟨hr, hnot⟩
      exact hRv (r, θ) (by
        by_contra hle
        exact hnot ⟨le_of_lt hr, not_lt.mp hle⟩)
    have hlim : Tendsto (fun s : ℝ ↦ φ ((s : ℂ) * unit θ)) atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop M] with s hs
      exact (hzero _ (hnorm (s, θ) hs)).symm
    rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont.continuousWithinAt hderiv hint hlim]
    simp
  -- The angular derivative integrates to zero along each circle.
  have hcircle : ∀ r ∈ Ioi (0 : ℝ), ∫ θ in Ioo (-π) π, T (r, θ) = 0 := by
    intro r hr
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
    have hderiv : ∀ θ : ℝ,
        HasDerivAt (fun s : ℝ ↦ φ ((r : ℂ) * unit s)) ((r : ℂ) * T (r, θ)) θ := by
      intro θ
      have h := (hφdiff _).comp_hasDerivAt θ (hasDerivAt_circle r θ)
      refine h.congr_deriv ?_
      simp only [T]
      rw [show (r : ℂ) * (I * unit θ) = r • (I * unit θ) from (Complex.real_smul ..).symm,
        map_smul, Complex.real_smul]
    have hTθ : Continuous (fun θ : ℝ ↦ (r : ℂ) * T (r, θ)) :=
      continuous_const.mul (hTc.comp (continuous_const.prodMk continuous_id))
    have hfun : (fun θ : ℝ ↦ T (r, θ)) = fun θ ↦ (r : ℂ)⁻¹ * ((r : ℂ) * T (r, θ)) := by
      funext θ
      field_simp
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le
      (by linarith [Real.pi_pos]), hfun, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ ↦ hderiv θ)
        (hTθ.intervalIntegrable _ _)]
    simp [unit]
  have hRint : ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, R p = -(2 * π : ℂ) * φ 0 := by
    rw [Measure.volume_eq_prod, setIntegral_prod _ hRi]
    rw [integral_integral_swap (by
      rw [Measure.prod_restrict]
      exact hRi)]
    simp_rw [hray]
    rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos]),
      Complex.real_smul]
    push_cast
    ring
  have hTint : ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, T p = 0 := by
    rw [Measure.volume_eq_prod, setIntegral_prod _ hTi]
    rw [setIntegral_congr_fun measurableSet_Ioi hcircle]
    simp
  rw [hpolar, integral_const_mul, integral_add hRi (hTi.const_mul I), integral_const_mul,
    hRint, hTint]
  ring

end

end SGPT.Foundations.Analysis.Pending.CauchyGreen
