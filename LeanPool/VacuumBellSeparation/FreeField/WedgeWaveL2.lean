/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WedgeWaveEntire
public import LeanPool.VacuumBellSeparation.FreeField.MassShellDistribution
public import LeanPool.VacuumBellSeparation.FreeField.ShellBoostMeasure

/-!
# Actual mass-shell L2 integrability throughout the closed wedge strip

The uniform integration-by-parts bound gives an integrable square majorant
against the original positive mass-shell measure. Real rapidity shifts
are then handled by the proved full measure-preserving shell boost.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped ENNReal

theorem continuous_wedgeWave_momentum (m : ℝ) (F : RealTestFunction) (ζ : ℂ) :
    Continuous (wedgeWave m F ζ) := by
  have hc : Continuous (fun q : EuclideanSpace ℝ (Fin 3) × Spacetime =>
      Complex.exp (Complex.I * boostPhase m (-ζ) q.1 q.2) * (F.1 q.2 : ℂ)) :=
    (Complex.continuous_exp.comp (continuous_const.mul
      (continuous_boostPhase_comp m (-ζ) continuous_fst continuous_snd))).mul
      (Complex.continuous_ofReal.comp ((continuous_testFunction F).comp continuous_snd))
  apply continuousOn_univ.mp
  exact continuousOn_integral_of_compact_support F.2.2 hc.continuousOn
    (fun p x _ hx => by simp only [image_eq_zero_of_notMem_tsupport hx,
      Complex.ofReal_zero, mul_zero])

theorem integrable_inv_dispersion_pow_four_massShell {m : ℝ} (hm : 0 < m) :
    Integrable (fun p : EuclideanSpace ℝ (Fin 3) => (dispersion m p ^ 4)⁻¹)
      (oneParticleMeasure m) :=
  ((integrable_inv_dispersion_pow_four hm.ne').smul_measure
    (c := (Real.toNNReal (1 / (2 * (2 * Real.pi) ^ 3 * m)) : ENNReal)) (by simp)).mono_measure
      (oneParticleMeasure_le_volume hm)

theorem maxCoordDerivNorm_nonneg (F : RealTestFunction) (N : ℕ) :
    0 ≤ maxCoordDerivNorm F N :=
  (integral_nonneg fun x => abs_nonneg (((dirDeriv (coordDir 0))^[N] F).1 x)).trans
    (le_maxCoordDerivNorm F N 0)

theorem memLp_wedgeWave_mul_I {m : ℝ} (hm : 0 < m) (F : RealTestFunction)
    (hF : tsupport F.1 ⊆ leftWedge 0) {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    MemLp (wedgeWave m F ((θ : ℂ) * Complex.I)) 2 (oneParticleMeasure m) := by
  have hc := continuous_wedgeWave_momentum m F ((θ : ℂ) * Complex.I)
  rw [memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable]
  apply ((integrable_inv_dispersion_pow_four_massShell hm).const_mul
    (16 * maxCoordDerivNorm F 2 ^ 2)).mono' (hc.norm.pow 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc
      ‖wedgeWave m F ((θ : ℂ) * Complex.I) p‖ ^ 2 ≤
          ((2 / dispersion m p) ^ 2 * maxCoordDerivNorm F 2) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_wedgeWave_mul_I_le hm F hF 2 hθ₀ hθπ p) 2
      _ = (16 * maxCoordDerivNorm F 2 ^ 2) * (dispersion m p ^ 4)⁻¹ := by ring

theorem wedgeWave_eq_imaginary_boost (m : ℝ) (F : RealTestFunction) (ζ : ℂ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    wedgeWave m F ζ p = wedgeWave m F ((ζ.im : ℂ) * Complex.I) (shellBoost m ζ.re p) := by
  simpa only [Complex.re_add_im] using
    wedgeWave_add_ofReal m ζ.re F ((ζ.im : ℂ) * Complex.I) p

theorem memLp_wedgeWave_closedStrip {m : ℝ} (hm : 0 < m) (F : RealTestFunction)
    (hF : tsupport F.1 ⊆ leftWedge 0) {ζ : ℂ} (hζ : 0 ≤ ζ.im ∧ ζ.im ≤ Real.pi) :
    MemLp (wedgeWave m F ζ) 2 (oneParticleMeasure m) := by
  have he : wedgeWave m F ζ =
      wedgeWave m F ((ζ.im : ℂ) * Complex.I) ∘ shellBoost m ζ.re :=
    funext (wedgeWave_eq_imaginary_boost m F ζ)
  rw [he]
  exact (memLp_wedgeWave_mul_I hm F hF hζ.1 hζ.2).comp_measurePreserving
    (measurePreserving_shellBoost hm ζ.re)

/-- Wedge wave L². -/
noncomputable def wedgeWaveL2 {m : ℝ} (hm : 0 < m) (F : RealTestFunction)
    (hF : tsupport F.1 ⊆ leftWedge 0) (ζ : ℂ) (hζ : 0 ≤ ζ.im ∧ ζ.im ≤ Real.pi) :
    Lp ℂ 2 (oneParticleMeasure m) :=
  (memLp_wedgeWave_closedStrip hm F hF hζ).toLp (wedgeWave m F ζ)

theorem wedgeWaveL2_ae {m : ℝ} (hm : 0 < m) (F : RealTestFunction)
    (hF : tsupport F.1 ⊆ leftWedge 0) (ζ : ℂ) (hζ : 0 ≤ ζ.im ∧ ζ.im ≤ Real.pi) :
    wedgeWaveL2 hm F hF ζ hζ =ᵐ[oneParticleMeasure m] wedgeWave m F ζ :=
  (memLp_wedgeWave_closedStrip hm F hF hζ).coeFn_toLp

theorem wedgeWaveL2_zero {m : ℝ} (hm : 0 < m) (F : RealTestFunction)
    (hF : tsupport F.1 ⊆ leftWedge 0) :
    wedgeWaveL2 hm F hF 0 ⟨le_rfl, Real.pi_pos.le⟩ = oneParticleL2 hm F := by
  apply Lp.ext
  filter_upwards [wedgeWaveL2_ae hm F hF 0 ⟨le_rfl, Real.pi_pos.le⟩,
    coeFn_oneParticleL2 hm F] with p hp hF
  rw [hp, hF, wedgeWave_zero]

/-- A bounded real-rapidity slab retains one common polynomial majorant.
This is the bound needed for local L2 continuity and holomorphy. -/
theorem norm_wedgeWave_closedStrip_le {m : ℝ} (hm : 0 < m) (F : RealTestFunction)
    (hF : tsupport F.1 ⊆ leftWedge 0) {ζ : ℂ} (hζ : 0 ≤ ζ.im ∧ ζ.im ≤ Real.pi)
    {B : ℝ} (hB : |ζ.re| ≤ B) (p : EuclideanSpace ℝ (Fin 3)) :
    ‖wedgeWave m F ζ p‖ ≤
      (2 * Real.exp B / dispersion m p) ^ 2 * maxCoordDerivNorm F 2 := by
  have hE := dispersion_pos hm.ne' (shellBoost m ζ.re p)
  have hω := dispersion_pos hm.ne' p
  have he : Real.exp (-B) * dispersion m p ≤ dispersion m (shellBoost m ζ.re p) := by
    have h := exp_neg_abs_mul_dispersion_le m (-ζ.re) p
    simp only [abs_neg, neg_neg] at h
    exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hB)) hω.le).trans h
  have henergy : dispersion m p ≤ Real.exp B * dispersion m (shellBoost m ζ.re p) := by
    calc
      dispersion m p = Real.exp B * (Real.exp (-B) * dispersion m p) := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left he (Real.exp_pos _).le
  have hratio : 2 / dispersion m (shellBoost m ζ.re p) ≤
      2 * Real.exp B / dispersion m p := by
    apply (div_le_div_iff₀ hE hω).mpr
    nlinarith
  rw [wedgeWave_eq_imaginary_boost]
  exact (norm_wedgeWave_mul_I_le hm F hF 2 hζ.1 hζ.2 _).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hratio 2)
      (maxCoordDerivNorm_nonneg F 2))

end VacuumBellSeparation
