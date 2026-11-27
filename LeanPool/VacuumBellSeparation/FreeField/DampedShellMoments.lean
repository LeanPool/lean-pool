/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialMassShellBound
public import LeanPool.VacuumBellSeparation.FreeField.MassShellDistribution
public import LeanPool.VacuumBellSeparation.FreeField.Lorentz
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Asymptotics

/-!
# Actual exponential damping and all energy moments on the physical mass shell

The radial Haar integrability theorem and the genuine Gamma-integral estimate
supply exponential norm integrability. The physical measure is dominated by
volume, and massive energy grows at infinity. Thus polynomial energy moments
of every exponentially damped physical L² vector are genuinely integrable.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter Topology Asymptotics
open scoped ComplexConjugate

theorem integrable_spatial_exp_neg_norm {a : ℝ} (ha : 0 < a) :
    Integrable (fun p : EuclideanSpace ℝ (Fin 3) => Real.exp (-a * ‖p‖)) := by
  apply (integrable_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 3)))
    (f := fun r : ℝ => Real.exp (-a * r))).mpr
  simpa [finrank_euclideanSpace, smul_eq_mul, Real.rpow_two, Real.rpow_one] using
    integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 2) (b := a)
      (by norm_num) (by norm_num) ha

theorem integrable_massShell_exp_neg_energy {m a : ℝ} (hm : 0 < m) (ha : 0 < a) :
    Integrable (fun p => Real.exp (-a * dispersion m p)) (oneParticleMeasure m) := by
  have hvol : Integrable (fun p => Real.exp (-a * dispersion m p)) := by
    apply (integrable_spatial_exp_neg_norm ha).mono'
    · exact ((continuous_const.mul (continuous_dispersion m)).rexp).aestronglyMeasurable
    · exact Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonpos_left (norm_le_dispersion m p) (by linarith)
  exact (hvol.smul_measure
    (c := (Real.toNNReal (1 / (2 * (2 * Real.pi) ^ 3 * m)) : ENNReal)) (by simp)).mono_measure
      (oneParticleMeasure_le_volume hm)

theorem tendsto_dispersion_cocompact (m : ℝ) :
    Tendsto (dispersion m) (cocompact (EuclideanSpace ℝ (Fin 3))) atTop :=
  tendsto_atTop_mono (norm_le_dispersion m) tendsto_norm_cocompact_atTop

theorem integrable_massShell_energy_pow_exp {m a : ℝ} (hm : 0 < m) (ha : 0 < a)
    (k : ℕ) :
    Integrable (fun p => dispersion m p ^ k * Real.exp (-a * dispersion m p))
      (oneParticleMeasure m) := by
  let := oneParticleMeasure_isLocallyFinite hm
  have hbig : (fun p => dispersion m p ^ k * Real.exp (-a * dispersion m p))
      =O[cocompact (EuclideanSpace ℝ (Fin 3))]
      (fun p => Real.exp (-(a / 2) * dispersion m p)) := by
    simpa only [Function.comp_def, Real.rpow_natCast, mul_comm] using
      (isLittleO_exp_mul_rpow_of_lt (k : ℝ) (a := -a) (b := -(a / 2))
        (by linarith)).isBigO.comp_tendsto (tendsto_dispersion_cocompact m)
  have hc : Continuous
      (fun p => dispersion m p ^ k * Real.exp (-a * dispersion m p)) :=
    ((continuous_dispersion m).pow k).mul ((continuous_const.mul (continuous_dispersion m)).rexp)
  exact hc.locallyIntegrable.integrable_of_isBigO_cocompact hbig
    ((integrable_massShell_exp_neg_energy hm (half_pos ha)).integrableAtFilter _)

theorem memLp_massShell_energy_pow_exp {m a : ℝ} (hm : 0 < m) (ha : 0 < a)
    (k : ℕ) :
    MemLp (fun p => dispersion m p ^ k * Real.exp (-a * dispersion m p)) 2
      (oneParticleMeasure m) := by
  have hc : Continuous
      (fun p => dispersion m p ^ k * Real.exp (-a * dispersion m p)) :=
    ((continuous_dispersion m).pow k).mul ((continuous_const.mul (continuous_dispersion m)).rexp)
  rw [memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable]
  apply (integrable_massShell_energy_pow_exp hm (show 0 < 2 * a by positivity) (2 * k)).congr
  exact Eventually.of_forall fun p => by
    dsimp only
    rw [Real.norm_eq_abs, sq_abs, mul_pow, ← pow_mul]
    have hexp : Real.exp (-(2 * a) * dispersion m p) =
        Real.exp (-a * dispersion m p) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    ring

/-- Damped shell amplitude given by `(Real.exp (-a * dispersion m p) : ℂ) * conj (ψ p)`. -/
noncomputable def dampedShellAmplitude {m : ℝ} (a : ℝ)
    (ψ : Lp ℂ 2 (oneParticleMeasure m)) (p : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  (Real.exp (-a * dispersion m p) : ℂ) * conj (ψ p)

theorem integrable_dampedShellAmplitude_moment {m a : ℝ}
    (hm : 0 < m) (ha : 0 < a) (ψ : Lp ℂ 2 (oneParticleMeasure m)) (k : ℕ) :
    Integrable (fun p => dispersion m p ^ k * ‖dampedShellAmplitude a ψ p‖)
      (oneParticleMeasure m) := by
  apply ((memLp_massShell_energy_pow_exp hm ha k).integrable_mul (Lp.memLp ψ).norm).congr
  exact Eventually.of_forall fun p => by
    simp only [Pi.mul_apply, dampedShellAmplitude, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Complex.norm_conj]
    ring

theorem integrable_dampedShellAmplitude {m a : ℝ}
    (hm : 0 < m) (ha : 0 < a) (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    Integrable (dampedShellAmplitude a ψ) (oneParticleMeasure m) := by
  have hnorm : Integrable (fun p => ‖dampedShellAmplitude a ψ p‖) (oneParticleMeasure m) := by
    simpa only [pow_zero, one_mul] using integrable_dampedShellAmplitude_moment hm ha ψ 0
  apply (integrable_norm_iff ?_).mp hnorm
  have hc : Continuous (fun p => (Real.exp (-a * dispersion m p) : ℂ)) :=
    Complex.continuous_ofReal.comp ((continuous_const.mul (continuous_dispersion m)).rexp)
  exact hc.aestronglyMeasurable.mul (Lp.memLp ψ).aestronglyMeasurable.star

end VacuumBellSeparation
