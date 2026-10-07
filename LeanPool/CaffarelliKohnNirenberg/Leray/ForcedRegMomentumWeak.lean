/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegMomentumFrequency

/-!
# The weak form of the forced frequency representative

Integrating the one-frequency weak form over all frequencies, against a
family of tests with square-integrable transforms, gives the frequency form of
`eq:reg-momentum-forced`: for the time derivative `Φₜ` and the damped symbol
`λΦ` of the test, `-∫∫ Re⟨Y, Φₜ⟩ + ∫∫ Re⟨Y, λΦ⟩` equals the pairing of the
divergence source and the force with the Leray projection of the test.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace CKN.Leray

theorem norm_lam_smul (ξ : L2Vec3) (z : ComplexVec3) :
    ‖(forcedFourierLam ξ : ℂ) • z‖ = forcedFourierLam ξ * ‖z‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (forcedFourierLam_nonneg ξ)]

/-- The pairing of the divergence source with the projected test is
controlled by the tensor and the test with its damped symbol. -/
theorem abs_re_inner_divergence_leray_le (ξ : L2Vec3) (F : ComplexTensor3) (z : ComplexVec3) :
    |(inner ℂ (-((2 * Real.pi * Complex.I : ℂ) • tensorDivergenceLinear ξ F))
        (leraySymbol ξ z)).re| ≤
      (‖F‖ ^ 2 + (‖z‖ ^ 2 + (forcedFourierLam ξ * ‖z‖) ^ 2) / 2) / 2 := by
  rw [← inner_conj_symm, Complex.conj_re]
  have h1 := abs_re_inner_divergence_le ξ (leraySymbol ξ z) F
  have h2 : forcedFourierLam ξ * ‖leraySymbol ξ z‖ ^ 2 ≤ forcedFourierLam ξ * ‖z‖ ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (leraySymbol_norm_le ξ z) 2)
      (forcedFourierLam_nonneg ξ)
  have h3 : forcedFourierLam ξ * ‖z‖ ^ 2 ≤ (‖z‖ ^ 2 + (forcedFourierLam ξ * ‖z‖) ^ 2) / 2 := by
    nlinarith only [sq_nonneg (‖z‖ - forcedFourierLam ξ * ‖z‖)]
  linarith only [h1, h2, h3]

theorem abs_re_inner_leray_le (ξ : L2Vec3) (h z : ComplexVec3) :
    |(inner ℂ h (leraySymbol ξ z)).re| ≤ (‖h‖ ^ 2 + ‖z‖ ^ 2) / 2 := by
  have h1 := abs_re_inner_le_half h (leraySymbol ξ z)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) (leraySymbol_norm_le ξ z) 2
  linarith only [h1, h2]

/-- A time-square-integrable slice on a bounded interval is time-integrable. -/
theorem integrable_slice_of_sq {E : Type} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] {T : ℝ} {f : L2Vec3 × ℝ → E}
    (hf : Measurable f) (ξ : L2Vec3)
    (hsq : Integrable (fun s => ‖f (ξ, s)‖ ^ 2) (volume.restrict (Ioc (0 : ℝ) T))) :
    Integrable (fun s => ‖f (ξ, s)‖) (volume.restrict (Ioc (0 : ℝ) T)) := by
  have hμt : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) T)) := by
    refine ⟨?_⟩
    simp only [Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hmeas : AEStronglyMeasurable (fun s => f (ξ, s)) (volume.restrict (Ioc (0 : ℝ) T)) :=
    (hf.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact (((memLp_two_iff_integrable_sq_norm hmeas).2 hsq).integrable one_le_two).norm

/-- The frequency form of `eq:reg-momentum-forced`. -/
theorem forcedFourierRep_weak_identity {B : L2Vec3 → ComplexVec3}
    {Fh : L2Vec3 × ℝ → ComplexTensor3} {Hh : L2Vec3 × ℝ → ComplexVec3}
    (hBm : Measurable B) (hFh : Measurable Fh) (hHh : Measurable Hh) {T : ℝ} (hT : 0 ≤ T)
    {Φ Φt : L2Vec3 × ℝ → ComplexVec3} (hΦm : Measurable Φ) (hΦtm : Measurable Φt)
    (hderiv : ∀ ξ t, HasDerivAt (fun s => Φ (ξ, s)) (Φt (ξ, t)) t)
    (hcont : ∀ ξ, Continuous fun t => Φt (ξ, t)) (h0 : ∀ ξ, Φ (ξ, 0) = 0)
    (hTz : ∀ ξ, Φ (ξ, T) = 0)
    (hY : Integrable (fun p => ‖forcedFourierRep B Fh Hh p‖ ^ 2)
      (volume.prod (volume.restrict (Ioc 0 T))))
    (hF2 : Integrable (fun p => ‖Fh p‖ ^ 2) (volume.prod (volume.restrict (Ioc 0 T))))
    (hH2 : Integrable (fun p => ‖Hh p‖ ^ 2) (volume.prod (volume.restrict (Ioc 0 T))))
    (hΦ2 : Integrable (fun p => ‖Φ p‖ ^ 2) (volume.prod (volume.restrict (Ioc 0 T))))
    (hΦt2 : Integrable (fun p => ‖Φt p‖ ^ 2) (volume.prod (volume.restrict (Ioc 0 T))))
    (hΛ2 : Integrable (fun p : L2Vec3 × ℝ => (forcedFourierLam p.1 * ‖Φ p‖) ^ 2)
      (volume.prod (volume.restrict (Ioc 0 T)))) :
    IntegrableOn (fun t => ∫ ξ, (inner ℂ (forcedFourierRep B Fh Hh (ξ, t)) (Φt (ξ, t))).re)
      (Ioc 0 T) ∧
    IntegrableOn (fun t => ∫ ξ, (inner ℂ (forcedFourierRep B Fh Hh (ξ, t))
      ((forcedFourierLam ξ : ℂ) • Φ (ξ, t))).re) (Ioc 0 T) ∧
    IntegrableOn (fun t => ∫ ξ, (inner ℂ (-((2 * Real.pi * Complex.I : ℂ) •
      tensorDivergenceLinear ξ (Fh (ξ, t)))) (leraySymbol ξ (Φ (ξ, t)))).re) (Ioc 0 T) ∧
    IntegrableOn (fun t => ∫ ξ, (inner ℂ (Hh (ξ, t)) (leraySymbol ξ (Φ (ξ, t)))).re)
      (Ioc 0 T) ∧
    -(∫ t in Ioc 0 T, ∫ ξ, (inner ℂ (forcedFourierRep B Fh Hh (ξ, t)) (Φt (ξ, t))).re) +
        (∫ t in Ioc 0 T, ∫ ξ, (inner ℂ (forcedFourierRep B Fh Hh (ξ, t))
          ((forcedFourierLam ξ : ℂ) • Φ (ξ, t))).re) =
      (∫ t in Ioc 0 T, ∫ ξ, (inner ℂ (-((2 * Real.pi * Complex.I : ℂ) •
          tensorDivergenceLinear ξ (Fh (ξ, t)))) (leraySymbol ξ (Φ (ξ, t)))).re) +
        ∫ t in Ioc 0 T, ∫ ξ, (inner ℂ (Hh (ξ, t)) (leraySymbol ξ (Φ (ξ, t)))).re := by
  set Y := forcedFourierRep B Fh Hh with hYdef
  have hYm : Measurable Y := (stronglyMeasurable_forcedFourierRep hBm hFh hHh).measurable
  let A : L2Vec3 × ℝ → ℝ := fun p => (inner ℂ (Y p) (Φt p)).re
  let Bf : L2Vec3 × ℝ → ℝ := fun p => (inner ℂ (Y p) ((forcedFourierLam p.1 : ℂ) • Φ p)).re
  let D : L2Vec3 × ℝ → ComplexVec3 := fun p =>
    -((2 * Real.pi * Complex.I : ℂ) • tensorDivergenceLinear p.1 (Fh p))
  let LΦ : L2Vec3 × ℝ → ComplexVec3 := fun p => leraySymbol p.1 (Φ p)
  let C : L2Vec3 × ℝ → ℝ := fun p => (inner ℂ (D p) (LΦ p)).re
  let E : L2Vec3 × ℝ → ℝ := fun p => (inner ℂ (Hh p) (LΦ p)).re
  have hDm : Measurable D := measurable_forcedFourierDivergence hFh
  have hLΦm : Measurable LΦ := by
    have h := measurable_leraySymbol_uncurry.comp (measurable_fst.prodMk hΦm)
    exact h
  have hlamm : Measurable fun p : L2Vec3 × ℝ => (forcedFourierLam p.1 : ℂ) • Φ p := by
    have h1 : Measurable fun p : L2Vec3 × ℝ => (forcedFourierLam p.1 : ℂ) := by
      unfold forcedFourierLam
      fun_prop
    exact h1.smul hΦm
  have hAm : Measurable A :=
    Complex.measurable_re.comp (continuous_inner.measurable.comp (hYm.prodMk hΦtm))
  have hBm' : Measurable Bf :=
    Complex.measurable_re.comp (continuous_inner.measurable.comp (hYm.prodMk hlamm))
  have hCm : Measurable C :=
    Complex.measurable_re.comp (continuous_inner.measurable.comp (hDm.prodMk hLΦm))
  have hEm : Measurable E :=
    Complex.measurable_re.comp (continuous_inner.measurable.comp (hHh.prodMk hLΦm))
  have hAint : Integrable A (volume.prod (volume.restrict (Ioc 0 T))) :=
    Integrable.mono' ((hY.add hΦt2).div_const 2) hAm.aestronglyMeasurable
      (Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs]; exact abs_re_inner_le_half (Y p) (Φt p))
  have hBint : Integrable Bf (volume.prod (volume.restrict (Ioc 0 T))) :=
    Integrable.mono' ((hY.add hΛ2).div_const 2) hBm'.aestronglyMeasurable
      (Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs]
        have h := abs_re_inner_le_half (Y p) ((forcedFourierLam p.1 : ℂ) • Φ p)
        rwa [norm_lam_smul] at h)
  have hCint : Integrable C (volume.prod (volume.restrict (Ioc 0 T))) :=
    Integrable.mono' ((hF2.add ((hΦ2.add hΛ2).div_const 2)).div_const 2)
      hCm.aestronglyMeasurable (Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs]
        exact abs_re_inner_divergence_leray_le p.1 (Fh p) (Φ p))
  have hEint : Integrable E (volume.prod (volume.restrict (Ioc 0 T))) :=
    Integrable.mono' ((hH2.add hΦ2).div_const 2) hEm.aestronglyMeasurable
      (Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs]; exact abs_re_inner_leray_le p.1 (Hh p) (Φ p))
  have hfreq : ∀ᵐ ξ ∂(volume : Measure L2Vec3),
      -(∫ t in Ioc 0 T, A (ξ, t)) + (∫ t in Ioc 0 T, Bf (ξ, t)) =
        (∫ t in Ioc 0 T, C (ξ, t)) + ∫ t in Ioc 0 T, E (ξ, t) := by
    filter_upwards [hF2.prod_right_ae, hH2.prod_right_ae, hAint.prod_right_ae,
      hBint.prod_right_ae, hCint.prod_right_ae, hEint.prod_right_ae]
      with ξ hFξ hHξ hAξ hBξ hCξ hEξ
    have hF1 := integrable_slice_of_sq hFh ξ hFξ
    have hH1 := integrable_slice_of_sq hHh ξ hHξ
    have hsrc : IntegrableOn (fun s => forcedFourierSource Fh Hh (ξ, s)) (Ioc 0 T) := by
      refine Integrable.mono' ((hF1.const_mul (2 * Real.pi * ‖ξ‖)).add hH1) ?_ ?_
      · exact ((measurable_forcedFourierSource hFh hHh).comp
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      · refine Eventually.of_forall fun s => ?_
        simp only [forcedFourierSource]
        exact (norm_add_le _ _).trans (add_le_add
          (norm_tensorDivergence_source_le ξ (Fh (ξ, s))) le_rfl)
    have hid := forcedFourierRep_test_identity (B := B) ξ hT hsrc (hderiv ξ) (hcont ξ)
      (h0 ξ) (hTz ξ)
    have hL : ∫ t in Ioc 0 T, (inner ℂ (Y (ξ, t))
        (-Φt (ξ, t) + (forcedFourierLam ξ : ℂ) • Φ (ξ, t))).re =
        -(∫ t in Ioc 0 T, A (ξ, t)) + ∫ t in Ioc 0 T, Bf (ξ, t) := by
      rw [← integral_neg, show (∫ t in Ioc 0 T, -A (ξ, t)) + ∫ t in Ioc 0 T, Bf (ξ, t) =
        ∫ t in Ioc 0 T, (-A (ξ, t) + Bf (ξ, t)) from (integral_add hAξ.neg hBξ).symm]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [A, Bf, inner_add_right, inner_neg_right, Complex.add_re, Complex.neg_re]
    have hR : ∫ t in Ioc 0 T, (inner ℂ (leraySymbol ξ (forcedFourierSource Fh Hh (ξ, t)))
        (Φ (ξ, t))).re = (∫ t in Ioc 0 T, C (ξ, t)) + ∫ t in Ioc 0 T, E (ξ, t) := by
      rw [show (∫ t in Ioc 0 T, C (ξ, t)) + ∫ t in Ioc 0 T, E (ξ, t) =
        ∫ t in Ioc 0 T, (C (ξ, t) + E (ξ, t)) from (integral_add hCξ hEξ).symm]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [C, E, D, LΦ]
      rw [leraySymbol, Submodule.inner_starProjection_left_eq_right, forcedFourierSource,
        inner_add_left, Complex.add_re]
    rw [← hL, ← hR]
    exact hid
  have hint := integral_congr_ae hfreq
  have e1 : ∫ ξ, (-(∫ t in Ioc 0 T, A (ξ, t)) + ∫ t in Ioc 0 T, Bf (ξ, t)) =
      -(∫ ξ, ∫ t in Ioc 0 T, A (ξ, t)) + ∫ ξ, ∫ t in Ioc 0 T, Bf (ξ, t) := by
    rw [← integral_neg]
    exact integral_add hAint.integral_prod_left.neg hBint.integral_prod_left
  have e2 : ∫ ξ, ((∫ t in Ioc 0 T, C (ξ, t)) + ∫ t in Ioc 0 T, E (ξ, t)) =
      (∫ ξ, ∫ t in Ioc 0 T, C (ξ, t)) + ∫ ξ, ∫ t in Ioc 0 T, E (ξ, t) :=
    integral_add hCint.integral_prod_left hEint.integral_prod_left
  rw [e1, e2] at hint
  refine ⟨hAint.integral_prod_right, hBint.integral_prod_right, hCint.integral_prod_right,
    hEint.integral_prod_right, ?_⟩
  rw [integral_integral_swap (f := fun ξ t => A (ξ, t)) hAint,
    integral_integral_swap (f := fun ξ t => Bf (ξ, t)) hBint,
    integral_integral_swap (f := fun ξ t => C (ξ, t)) hCint,
    integral_integral_swap (f := fun ξ t => E (ξ, t)) hEint] at hint
  exact hint

end CKN.Leray

end
