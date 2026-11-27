/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.OneParticle
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Decay of the one-particle wave functions

Integrability in the one-particle definitions:

* `spatialDeriv F v`: the spatial directional derivative `∂_v F` of a real test function, again
  a real test function;
* `oneParticle_spatialDeriv`: `κ_m(∂_v F)(𝐩) = i ⟪𝐩, v⟫ κ_m F(𝐩)` (integration by parts on
  spacetime; the boundary terms vanish by compact support);
* `norm_oneParticle_le_div`: `|κ_m F(𝐩)| ≤ C_F / (1 + |𝐩|²)`;
* `continuous_oneParticle`: `κ_m F` is continuous in `𝐩`;
* `integrable_oneParticleInner_integrand`: for `m > 0` the integrand of `oneParticleInner m F G`
  is integrable.
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate

namespace VacuumBellSeparation

theorem differentiable_testFunction (F : RealTestFunction) : Differentiable ℝ F.1 := by
  exact (contDiff_infty_iff_fderiv.1 F.2.1).1

/-- The spatial directional derivative `∂_v F` of a real test function, again a test function. -/
noncomputable def spatialDeriv (F : RealTestFunction) (v : EuclideanSpace ℝ (Fin 3)) :
    RealTestFunction :=
  ⟨fun x => fderiv ℝ F.1 x ((0 : ℝ), v),
    (contDiff_infty_iff_fderiv.1 F.2.1).2.clm_apply contDiff_const,
    F.2.2.fderiv_apply ℝ ((0 : ℝ), v)⟩

theorem spatialDeriv_apply (F : RealTestFunction) (v : EuclideanSpace ℝ (Fin 3))
    (x : Spacetime) : (spatialDeriv F v).1 x = fderiv ℝ F.1 x ((0 : ℝ), v) := rfl

/-- The phase `x ↦ i (ω_m(𝐩) x⁰ - ⟪𝐩, 𝐱⟫)` of the plane wave, as a real-linear map. -/
noncomputable def phaseCLM (m : ℝ) (p : EuclideanSpace ℝ (Fin 3)) : Spacetime →L[ℝ] ℂ :=
  Complex.I • (Complex.ofRealCLM.comp
    (dispersion m p • ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin 3)) -
      (innerSL ℝ p).comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin 3)))))

theorem phaseCLM_apply (m : ℝ) (p : EuclideanSpace ℝ (Fin 3)) (x : Spacetime) :
    phaseCLM m p x = Complex.I * ((dispersion m p * x.1 - ⟪p, x.2⟫_ℝ : ℝ) : ℂ) := by
  simp [phaseCLM]

/-- `κ_m(∂_v F)(𝐩) = i ⟪𝐩, v⟫ κ_m F(𝐩)`. -/
theorem oneParticle_spatialDeriv (m : ℝ) (F : RealTestFunction)
    (v p : EuclideanSpace ℝ (Fin 3)) :
    oneParticle m (spatialDeriv F v) p = Complex.I * (⟪p, v⟫_ℝ : ℂ) * oneParticle m F p := by
  have hD0 : phaseCLM m p ((0 : ℝ), v) = -(Complex.I * (⟪p, v⟫_ℝ : ℂ)) := by
    simp [phaseCLM_apply]
  have hg : ∀ x : Spacetime, HasFDerivAt (fun y => ((F.1 y : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ F.1 x)) x := fun x =>
    Complex.ofRealCLM.hasFDerivAt.comp x ((differentiable_testFunction F x).hasFDerivAt)
  have he : ∀ x : Spacetime, HasFDerivAt (fun y => Complex.exp (phaseCLM m p y))
      (Complex.exp (phaseCLM m p x) • phaseCLM m p) x := fun x =>
    (phaseCLM m p).hasFDerivAt.cexp
  have hfd : ∀ x : Spacetime,
      fderiv ℝ (fun y => Complex.exp (phaseCLM m p y)) x ((0 : ℝ), v) =
        -(Complex.I * (⟪p, v⟫_ℝ : ℂ)) * Complex.exp (phaseCLM m p x) := by
    intro x
    rw [(he x).fderiv, smul_apply, hD0, smul_eq_mul]
    ring
  have hgd : ∀ x : Spacetime, fderiv ℝ (fun y => ((F.1 y : ℝ) : ℂ)) x ((0 : ℝ), v) =
      (((spatialDeriv F v).1 x : ℝ) : ℂ) := by
    intro x
    rw [(hg x).fderiv]
    rfl
  have hfun1 : (fun x : Spacetime =>
      fderiv ℝ (fun y => Complex.exp (phaseCLM m p y)) x ((0 : ℝ), v) * ((F.1 x : ℝ) : ℂ)) =
      fun x => -(Complex.I * (⟪p, v⟫_ℝ : ℂ)) * oneParticleIntegrand m F p x := by
    funext x
    rw [hfd]
    simp only [oneParticleIntegrand, phaseCLM_apply]
    ring
  have hfun2 : (fun x : Spacetime =>
      Complex.exp (phaseCLM m p x) * fderiv ℝ (fun y => ((F.1 y : ℝ) : ℂ)) x ((0 : ℝ), v)) =
      oneParticleIntegrand m (spatialDeriv F v) p := by
    funext x
    rw [hgd]
    simp only [oneParticleIntegrand, phaseCLM_apply]
  have hfun3 : (fun x : Spacetime => Complex.exp (phaseCLM m p x) * ((F.1 x : ℝ) : ℂ)) =
      oneParticleIntegrand m F p := by
    funext x
    simp only [oneParticleIntegrand, phaseCLM_apply]
  have hint1 : MeasureTheory.Integrable (fun x : Spacetime =>
      fderiv ℝ (fun y => Complex.exp (phaseCLM m p y)) x ((0 : ℝ), v) * ((F.1 x : ℝ) : ℂ)) := by
    rw [hfun1]
    exact (integrable_oneParticleIntegrand m F p).const_mul _
  have hint2 : MeasureTheory.Integrable (fun x : Spacetime =>
      Complex.exp (phaseCLM m p x) * fderiv ℝ (fun y => ((F.1 y : ℝ) : ℂ)) x ((0 : ℝ), v)) := by
    rw [hfun2]
    exact integrable_oneParticleIntegrand m (spatialDeriv F v) p
  have hint3 : MeasureTheory.Integrable
      (fun x : Spacetime => Complex.exp (phaseCLM m p x) * ((F.1 x : ℝ) : ℂ)) := by
    rw [hfun3]
    exact integrable_oneParticleIntegrand m F p
  have : (MeasureTheory.volume : MeasureTheory.Measure Spacetime).IsAddHaarMeasure :=
    MeasureTheory.Measure.prod.instIsAddHaarMeasure _ _
  have key : ∫ x : Spacetime,
      Complex.exp (phaseCLM m p x) * fderiv ℝ (fun y => ((F.1 y : ℝ) : ℂ)) x ((0 : ℝ), v) =
      - ∫ x : Spacetime,
        fderiv ℝ (fun y => Complex.exp (phaseCLM m p y)) x ((0 : ℝ), v) * ((F.1 x : ℝ) : ℂ) :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hint1 hint2 hint3
      (fun x _ => (he x).differentiableAt) (fun x _ => (hg x).differentiableAt)
  calc oneParticle m (spatialDeriv F v) p
      = ∫ x : Spacetime,
          Complex.exp (phaseCLM m p x) * fderiv ℝ (fun y => ((F.1 y : ℝ) : ℂ)) x ((0 : ℝ), v) := by
        rw [oneParticle_eq_integral, hfun2]
    _ = - ∫ x : Spacetime,
          fderiv ℝ (fun y => Complex.exp (phaseCLM m p y)) x ((0 : ℝ), v) * ((F.1 x : ℝ) : ℂ) :=
        key
    _ = - ∫ x : Spacetime, -(Complex.I * (⟪p, v⟫_ℝ : ℂ)) * oneParticleIntegrand m F p x := by
        rw [hfun1]
    _ = Complex.I * (⟪p, v⟫_ℝ : ℂ) * oneParticle m F p := by
        rw [MeasureTheory.integral_const_mul, oneParticle_eq_integral]
        ring

/-! ### Decay in the momentum -/

/-- The second spatial derivative `∂_j ∂_j F` along the `j`-th coordinate axis. -/
noncomputable def spatialDeriv2 (F : RealTestFunction) (j : Fin 3) : RealTestFunction :=
  spatialDeriv (spatialDeriv F (EuclideanSpace.single j 1)) (EuclideanSpace.single j 1)

theorem inner_euclideanSingle_one (p : EuclideanSpace ℝ (Fin 3)) (j : Fin 3) :
    ⟪p, EuclideanSpace.single j (1 : ℝ)⟫_ℝ = p j := by
  simp [EuclideanSpace.inner_single_right]

/-- `κ_m(∂_j ∂_j F)(𝐩) = -p_j² κ_m F(𝐩)`. -/
theorem oneParticle_spatialDeriv2 (m : ℝ) (F : RealTestFunction) (j : Fin 3)
    (p : EuclideanSpace ℝ (Fin 3)) :
    oneParticle m (spatialDeriv2 F j) p = -(((p j : ℝ) : ℂ) ^ 2) * oneParticle m F p := by
  rw [spatialDeriv2, oneParticle_spatialDeriv, oneParticle_spatialDeriv, inner_euclideanSingle_one]
  linear_combination (((p j : ℝ) : ℂ) ^ 2 * oneParticle m F p) * Complex.I_sq

/-- Decay of the one-particle wave function: `|κ_m F(𝐩)| ≤ C / (1 + |𝐩|²)`. -/
theorem norm_oneParticle_le_div (m : ℝ) (F : RealTestFunction) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p, ‖oneParticle m F p‖ ≤ C / (1 + ‖p‖ ^ 2) := by
  refine ⟨(∫ x, |F.1 x|) + ∑ j : Fin 3, ∫ x, |(spatialDeriv2 F j).1 x|, ?_, ?_⟩
  · exact add_nonneg (MeasureTheory.integral_nonneg fun x => abs_nonneg _)
      (Finset.sum_nonneg fun j _ => MeasureTheory.integral_nonneg fun x => abs_nonneg _)
  · intro p
    rw [le_div_iff₀ (by positivity)]
    have h1 : ∀ j : Fin 3, (p j) ^ 2 * ‖oneParticle m F p‖ ≤
        ∫ x, |(spatialDeriv2 F j).1 x| := by
      intro j
      have h := norm_oneParticle_le m (spatialDeriv2 F j) p
      rw [oneParticle_spatialDeriv2, norm_mul, norm_neg, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, sq_abs] at h
      exact h
    have h2 : ‖p‖ ^ 2 * ‖oneParticle m F p‖ ≤
        ∑ j : Fin 3, ∫ x, |(spatialDeriv2 F j).1 x| := by
      rw [EuclideanSpace.real_norm_sq_eq, Finset.sum_mul]
      exact Finset.sum_le_sum fun j _ => h1 j
    have h0 := norm_oneParticle_le m F p
    nlinarith [h0, h2]

/-! ### Integrability of the one-particle inner product -/

theorem continuous_dispersion (m : ℝ) : Continuous (dispersion m) := by
  change Continuous (fun p : EuclideanSpace ℝ (Fin 3) => Real.sqrt (m ^ 2 + ‖p‖ ^ 2))
  exact (continuous_const.add (continuous_norm.pow 2)).sqrt

theorem le_dispersion {m : ℝ} (hm : 0 ≤ m) (p : EuclideanSpace ℝ (Fin 3)) :
    m ≤ dispersion m p :=
  calc m = Real.sqrt (m ^ 2) := (Real.sqrt_sq hm).symm
    _ ≤ Real.sqrt (m ^ 2 + ‖p‖ ^ 2) :=
        Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
    _ = dispersion m p := rfl

theorem continuous_oneParticle (m : ℝ) (F : RealTestFunction) :
    Continuous (oneParticle m F) := by
  change Continuous fun p => ∫ x, oneParticleIntegrand m F p x
  refine MeasureTheory.continuous_of_dominated (bound := fun x => |F.1 x|)
    (fun p => (integrable_oneParticleIntegrand m F p).aestronglyMeasurable) ?_ ?_ ?_
  · intro p
    refine Filter.Eventually.of_forall fun x => le_of_eq ?_
    simp only [oneParticleIntegrand, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
  · exact ((continuous_testFunction F).integrable_of_hasCompactSupport F.2.2).abs
  · refine Filter.Eventually.of_forall fun x => ?_
    change Continuous fun p : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (Complex.I * ((dispersion m p * x.1 - ⟪p, x.2⟫_ℝ : ℝ) : ℂ)) * ((F.1 x : ℝ) : ℂ)
    exact (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      (((continuous_dispersion m).mul continuous_const).sub
        (continuous_id.inner continuous_const))))).mul continuous_const

/-- For `m > 0` the integrand of `oneParticleInner m F G` is integrable. -/
theorem integrable_oneParticleInner_integrand {m : ℝ} (hm : 0 < m) (F G : RealTestFunction) :
    MeasureTheory.Integrable (fun p => conj (oneParticle m F p) * oneParticle m G p *
      ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ)) := by
  obtain ⟨CF, hCF0, hCF⟩ := norm_oneParticle_le_div m F
  obtain ⟨CG, hCG0, hCG⟩ := norm_oneParticle_le_div m G
  have hc : 0 < 2 * (2 * Real.pi) ^ 3 := by positivity
  have hpos : ∀ p, 0 < dispersion m p := fun p => hm.trans_le (le_dispersion hm.le p)
  have hint : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) => ((1 : ℝ) + ‖p‖ ^ 2) ^ (-(4 : ℝ) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (by rw [finrank_euclideanSpace_fin]; norm_num)
  refine (hint.const_mul (CF * CG / (2 * (2 * Real.pi) ^ 3 * m))).mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    exact ((Complex.continuous_conj.comp (continuous_oneParticle m F)).mul
      (continuous_oneParticle m G)).mul (Complex.continuous_ofReal.comp
        (continuous_const.div (continuous_const.mul (continuous_dispersion m))
          fun p => (mul_pos hc (hpos p)).ne'))
  · refine Filter.Eventually.of_forall fun p => ?_
    have hq : 0 < 1 + ‖p‖ ^ 2 := by positivity
    have hw : 0 < 1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) :=
      one_div_pos.2 (mul_pos hc (hpos p))
    have hww : 1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) ≤
        1 / (2 * (2 * Real.pi) ^ 3 * m) :=
      one_div_le_one_div_of_le (mul_pos hc hm)
        (mul_le_mul_of_nonneg_left (le_dispersion hm.le p) hc.le)
    have hrw : ((1 : ℝ) + ‖p‖ ^ 2) ^ (-(4 : ℝ) / 2) = ((1 + ‖p‖ ^ 2)⁻¹) ^ 2 := by
      rw [show -(4 : ℝ) / 2 = -2 by norm_num, Real.rpow_neg hq.le, Real.rpow_two, inv_pow]
    have hab : ‖oneParticle m F p‖ * ‖oneParticle m G p‖ ≤
        CF / (1 + ‖p‖ ^ 2) * (CG / (1 + ‖p‖ ^ 2)) :=
      mul_le_mul (hCF p) (hCG p) (norm_nonneg _) (div_nonneg hCF0 hq.le)
    have habw : ‖oneParticle m F p‖ * ‖oneParticle m G p‖ *
        (1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p)) ≤
        CF / (1 + ‖p‖ ^ 2) * (CG / (1 + ‖p‖ ^ 2)) * (1 / (2 * (2 * Real.pi) ^ 3 * m)) :=
      mul_le_mul hab hww hw.le (mul_nonneg (div_nonneg hCF0 hq.le) (div_nonneg hCG0 hq.le))
    have hnorm : ‖conj (oneParticle m F p) * oneParticle m G p *
        ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ)‖ =
        ‖oneParticle m F p‖ * ‖oneParticle m G p‖ *
          (1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p)) := by
      rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hw]
    change ‖conj (oneParticle m F p) * oneParticle m G p *
        ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ)‖ ≤
      CF * CG / (2 * (2 * Real.pi) ^ 3 * m) * ((1 : ℝ) + ‖p‖ ^ 2) ^ (-(4 : ℝ) / 2)
    rw [hnorm, hrw]
    refine habw.trans (le_of_eq ?_)
    first
    | ring


end VacuumBellSeparation
