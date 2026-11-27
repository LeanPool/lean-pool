/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Complex.CauchyTransform
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The Cauchy–Pompeiu formula

For a compactly supported `C¹` function `g : ℂ → ℂ`, the Cauchy transform of `∂_zbar g` is `g`:
`C (∂_zbar g) (z) = (1/π) ∫ ∂_zbar g (w) / (z − w) dw = g (z)` for every `z ∈ ℂ`
(`HarmonicAnalysis.cauchyTransform_dzbar`). In other words, the Cauchy kernel `1 / (π z)` is a
fundamental solution of `∂_zbar`. This is the standard Cauchy–Pompeiu formula, for compactly
supported
functions (no boundary term).

The proof is the computation in polar coordinates around `z`. The substitution `w = z + ρ`
reduces the formula to `∫ ∂_zbar g (z + ρ) / ρ dρ = −π g (z)`. Write `ρ = r e^{iθ}`, let
`a (r, θ) = g (z + r e^{iθ})` and let `L` be the real derivative of `g` at `z + r e^{iθ}`.

* The Jacobian `r` cancels the singularity:
  `r ∂_zbar g (z + r e^{iθ}) / (r e^{iθ}) = ½ (L (e^{iθ}) + i L (i e^{iθ}))`.
* `L (e^{iθ}) = ∂_r a (r, θ)`, and its integral over `r ∈ (0, ∞)` is `−g (z)` (fundamental
  theorem of calculus; `g` has compact support).
* `L (i e^{iθ}) = r⁻¹ ∂_θ a (r, θ)`, and its integral over `θ ∈ (−π, π)` is `0` for `r > 0`,
  since `a (r, π) = a (r, −π)`.

Both terms are continuous in `(r, θ)` and vanish for large `r`, so Fubini's theorem applies:
`∫ ∂_zbar g (z + ρ) / ρ dρ = ½ · 2π · (−g (z)) = −π g (z)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Complex
open scoped Real Topology

namespace HarmonicAnalysis

/-- A real-linear map `L : ℂ → ℂ` is `L v = Re v · L 1 + Im v · L i`. -/
private lemma clm_apply_eq (L : ℂ →L[ℝ] ℂ) (v : ℂ) : L v = v.re * L 1 + v.im * L I := by
  have hv : v = v.re • (1 : ℂ) + v.im • I := by
    rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

/-- A real-linear map `L : ℂ → ℂ` commutes with real scalars: `L (r v) = r L v`. -/
private lemma clm_ofReal_mul (L : ℂ →L[ℝ] ℂ) (r : ℝ) (v : ℂ) : L (r * v) = r * L v := by
  rw [← Complex.real_smul, map_smul, Complex.real_smul]

/-- The unit vector `e^{iθ} = cos θ + i sin θ`. -/
private def unitVec (θ : ℝ) : ℂ := Real.cos θ + Real.sin θ * I

/-- The integrand in polar coordinates: for `r ≠ 0`, `e = e^{iθ}` and a real-linear `L` (the
derivative of `g` at `z + r e`), `r · ½ (L 1 + i L i) / (r e) = ½ (L e + i L (i e))`. -/
private lemma polar_integrand (L : ℂ →L[ℝ] ℂ) {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    r • ((2⁻¹ : ℂ) • (L 1 + I • L I) * (r * unitVec θ)⁻¹) =
      2⁻¹ * (L (unitVec θ) + I * L (I * unitVec θ)) := by
  unfold unitVec
  have hcs : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  have he : ((Real.cos θ : ℂ) + Real.sin θ * I)⁻¹ = Real.cos θ - Real.sin θ * I :=
    inv_eq_of_mul_eq_one_right (by linear_combination hcs - (Real.sin θ : ℂ) ^ 2 * I_sq)
  rw [clm_apply_eq L (_ + _), clm_apply_eq L (I * _)]
  simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, mul_one, zero_sub, ofReal_neg]
  rw [mul_inv, he, Complex.real_smul, smul_eq_mul, smul_eq_mul]
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr
  field_simp
  linear_combination (-(L I * Real.sin θ)) * I_sq

/-- `|e^{iθ}| = 1`. -/
private lemma norm_unitVec (θ : ℝ) : ‖unitVec θ‖ = 1 := by
  rw [unitVec, ofReal_cos, ofReal_sin]
  exact norm_cos_add_sin_mul_I θ

/-- `θ ↦ e^{iθ}` is continuous. -/
private lemma continuous_unitVec : Continuous unitVec := by
  unfold unitVec
  fun_prop

/-- `d/dθ e^{iθ} = i e^{iθ}`. -/
private lemma hasDerivAt_unitVec (θ : ℝ) : HasDerivAt unitVec (I * unitVec θ) θ := by
  have h := (Real.hasDerivAt_cos θ).ofReal_comp.add
    ((Real.hasDerivAt_sin θ).ofReal_comp.mul_const I)
  have he : I * unitVec θ = ↑(-Real.sin θ) + ↑(Real.cos θ) * I := by
    rw [unitVec, ofReal_neg]
    linear_combination (Real.sin θ : ℂ) * I_sq
  rw [he]
  exact h

/-- `e^{iπ} = e^{−iπ}`. -/
private lemma unitVec_pi : unitVec π = unitVec (-π) := by
  simp [unitVec]

/-- If `tsupport g ⊆ B (0, M)` and `r > M + |z|`, then `z + r e^{iθ}` lies outside the support
of `g`. -/
private lemma add_mul_unitVec_notMem {g : ℂ → ℂ} {M : ℝ}
    (hM : tsupport g ⊆ Metric.closedBall 0 M) (z : ℂ) {r : ℝ} (hr : M + ‖z‖ < r) (θ : ℝ) :
    z + r * unitVec θ ∉ tsupport g := by
  intro h
  have h1 := mem_closedBall_zero_iff.1 (hM h)
  have h2 : ‖(r : ℂ) * unitVec θ‖ ≤ ‖z + r * unitVec θ‖ + ‖z‖ := by
    calc ‖(r : ℂ) * unitVec θ‖ = ‖(z + r * unitVec θ) - z‖ := by ring_nf
      _ ≤ _ := norm_sub_le _ _
  rw [norm_mul, norm_unitVec, mul_one, Complex.norm_real, Real.norm_eq_abs] at h2
  linarith [le_abs_self r]

/-- A continuous function of `(r, θ)` that vanishes for `r > R` is integrable on the target
`(0, ∞) × (−π, π)` of the polar coordinates. -/
private lemma integrableOn_polarTarget {F : ℝ × ℝ → ℂ} (hF : Continuous F) {R : ℝ}
    (hR : ∀ p : ℝ × ℝ, R < p.1 → F p = 0) :
    IntegrableOn F (Ioi 0 ×ˢ Ioo (-π) π) := by
  refine (hF.continuousOn.integrableOn_compact (K := Icc 0 R ×ˢ Icc (-π) π)
    (isCompact_Icc.prod isCompact_Icc)).of_forall_sdiff_eq_zero
    (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => hR p ?_
  obtain ⟨⟨h0, hθ⟩, hn⟩ := hp
  by_contra h
  exact hn ⟨⟨le_of_lt h0, not_lt.1 h⟩, ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩⟩

/-- A continuous function on `ℝ` that vanishes on `(R, ∞)` is integrable on `(0, ∞)`. -/
private lemma integrableOn_Ioi_of_eq_zero {φ : ℝ → ℂ} (hφ : Continuous φ) {R : ℝ}
    (hR : ∀ r, R < r → φ r = 0) : IntegrableOn φ (Ioi 0) := by
  refine (hφ.continuousOn.integrableOn_compact (K := Icc 0 R)
    isCompact_Icc).of_forall_sdiff_eq_zero measurableSet_Ioi fun r hr => hR r ?_
  obtain ⟨h0, hn⟩ := hr
  by_contra h
  exact hn ⟨le_of_lt h0, not_lt.1 h⟩

/-- `∫ ∂_zbar g (z + ρ) / ρ dρ = −π g (z)`, in polar coordinates `ρ = r e^{iθ}` around `z`. -/
private lemma integral_dzbar_mul_inv {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (z : ℂ) : ∫ ρ, dzbar g (z + ρ) * ρ⁻¹ = -(π * g z) := by
  obtain ⟨M, hM⟩ := hgc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  have hD : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hdiff : Differentiable ℝ g := hg.differentiable one_ne_zero
  set b : ℝ × ℝ → ℂ := fun p => fderiv ℝ g (z + p.1 * unitVec p.2) (unitVec p.2)
  set c : ℝ × ℝ → ℂ := fun p => fderiv ℝ g (z + p.1 * unitVec p.2) (I * unitVec p.2)
  have hu := continuous_unitVec
  have hb : Continuous b := by fun_prop
  have hc : Continuous c := by fun_prop
  have hfar : ∀ p : ℝ × ℝ, M + ‖z‖ < p.1 → fderiv ℝ g (z + p.1 * unitVec p.2) = 0 :=
    fun p hp => fderiv_of_notMem_tsupport ℝ (add_mul_unitVec_notMem hM z hp p.2)
  have hbi : IntegrableOn b (Ioi 0 ×ˢ Ioo (-π) π) :=
    integrableOn_polarTarget hb (R := M + ‖z‖) fun p hp => by simp [b, hfar p hp]
  have hci : IntegrableOn c (Ioi 0 ×ˢ Ioo (-π) π) :=
    integrableOn_polarTarget hc (R := M + ‖z‖) fun p hp => by simp [c, hfar p hp]
  have hprod : (volume : Measure (ℝ × ℝ)).restrict (Ioi 0 ×ˢ Ioo (-π) π) =
      (volume.restrict (Ioi 0)).prod (volume.restrict (Ioo (-π) π)) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  -- The `r`-integral of `b = ∂_r g (z + r e^{iθ})` is `−g (z)`.
  have hB : ∫ p in Ioi 0 ×ˢ Ioo (-π) π, b p = (2 * π : ℝ) • -g z := by
    have hinner : ∀ θ : ℝ, ∫ r in Ioi (0 : ℝ), b (r, θ) = -g z := by
      intro θ
      have hderiv : ∀ r : ℝ, HasDerivAt (fun r : ℝ => g (z + r * unitVec θ)) (b (r, θ)) r := by
        intro r
        have h1 : HasDerivAt (fun r : ℝ => z + r * unitVec θ) (unitVec θ) r := by
          simpa using ((hasDerivAt_id r).ofReal_comp.mul_const (unitVec θ)).const_add z
        exact (hdiff _).hasFDerivAt.comp_hasDerivAt r h1
      have h := integral_Ioi_of_hasDerivAt_of_tendsto (m := 0)
        (hderiv 0).continuousAt.continuousWithinAt (fun r _ => hderiv r)
        (integrableOn_Ioi_of_eq_zero (hb.comp (Continuous.prodMk_left θ)) (R := M + ‖z‖)
          fun r hr => by simp [b, hfar (r, θ) hr])
        (tendsto_const_nhds.congr' ((eventually_gt_atTop (M + ‖z‖)).mono fun r hr =>
          (image_eq_zero_of_notMem_tsupport (add_mul_unitVec_notMem hM z hr θ)).symm))
      simpa using h
    rw [IntegrableOn, hprod] at hbi
    rw [hprod, integral_prod_symm b hbi]
    simp_rw [hinner]
    rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
    ring_nf
  -- The `θ`-integral of `c = r⁻¹ ∂_θ g (z + r e^{iθ})` vanishes, by periodicity.
  have hC : ∫ p in Ioi 0 ×ˢ Ioo (-π) π, c p = 0 := by
    have hinner : ∀ r : ℝ, r ≠ 0 → ∫ θ in Ioo (-π) π, c (r, θ) = 0 := by
      intro r hr
      have hderiv : ∀ θ : ℝ,
          HasDerivAt (fun θ : ℝ => g (z + r * unitVec θ)) (r * c (r, θ)) θ := by
        intro θ
        have h1 : HasDerivAt (fun θ : ℝ => z + r * unitVec θ) (r * (I * unitVec θ)) θ :=
          ((hasDerivAt_unitVec θ).const_mul (r : ℂ)).const_add z
        have h := (hdiff _).hasFDerivAt.comp_hasDerivAt θ h1
        rwa [clm_ofReal_mul] at h
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := -π) (b := π)
        (fun θ _ => hderiv θ)
        ((continuous_const.mul (hc.comp (Continuous.prodMk_right r))).intervalIntegrable _ _)
      rw [intervalIntegral.integral_const_mul, unitVec_pi, sub_self,
        intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
        integral_Ioc_eq_integral_Ioo] at h
      exact (mul_eq_zero.1 h).resolve_left (ofReal_ne_zero.2 hr)
    rw [IntegrableOn, hprod] at hci
    rw [hprod, integral_prod c hci, ← integral_zero ℝ ℂ]
    exact setIntegral_congr_fun measurableSet_Ioi fun r hr => hinner r (ne_of_gt hr)
  rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target,
    setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      (g := fun p => 2⁻¹ * (b p + I * c p)) fun p hp => ?_]
  · rw [integral_const_mul, integral_add hbi (hci.const_mul I), integral_const_mul, hB, hC]
    rw [Complex.real_smul]
    push_cast
    ring
  · simp only [Complex.polarCoord_symm_apply, dzbar]
    exact polar_integrand _ (ne_of_gt hp.1) p.2

/-- **The Cauchy–Pompeiu formula**: the Cauchy transform inverts `∂_zbar` on compactly supported
`C¹` functions, `C (∂_zbar g) (z) = (1/π) ∫ ∂_zbar g (w) / (z − w) dw = g (z)`. -/
theorem cauchyTransform_dzbar {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (z : ℂ) : cauchyTransform (dzbar g) z = g z := by
  rw [cauchyTransform_apply,
    ← integral_add_left_eq_self (fun w => dzbar g w * cauchyKernel (z - w)) z]
  have h : ∀ ρ : ℂ, dzbar g (z + ρ) * cauchyKernel (z - (z + ρ)) =
      -(π : ℂ)⁻¹ * (dzbar g (z + ρ) * ρ⁻¹) := by
    intro ρ
    rw [cauchyKernel, sub_add_cancel_left, mul_neg, inv_neg, mul_inv]
    ring
  simp_rw [h]
  rw [integral_const_mul, integral_dzbar_mul_inv hg hgc z]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp

end HarmonicAnalysis
