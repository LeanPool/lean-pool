/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.CompactDistributionCoefficients
public import LeanPool.VacuumBellSeparation.FreeField.SchwartzSeries
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Entire cutoff exponentials evaluated by actual distributions

The exponential family is built as actual compactly supported Schwartz
functions. Its polynomial series converges in the Schwartz topology by the
smooth-series construction; scalar absolute convergence and continuity then
give genuine scalar power series at every basepoint. This proves entireness
of the cutoff pairing.
-/

@[expose] public section

open Filter Topology
open scoped SchwartzMap

namespace VacuumBellSeparation

/-- The literal compact Schwartz function `exp(z a(x)) φ(x)`. -/
noncomputable def spatialSchwartzExponential
    (a : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (hφ : HasCompactSupport φ) (z : ℂ) :
    SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ :=
  (show HasCompactSupport (fun x => Complex.exp (z *
    (a x : ℂ)) * φ x) from hφ.mul_left).toSchwartzMap ((Complex.contDiff_exp.comp
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp a.contDiff))).mul (φ.smooth ⊤))

@[simp] theorem spatialSchwartzExponential_apply
    (a : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (hφ : HasCompactSupport φ)
    (z : ℂ) (x : EuclideanSpace ℝ (Fin 3)) :
    spatialSchwartzExponential a φ hφ z x = Complex.exp (z * (a x : ℂ)) * φ x := rfl

theorem hasCompactSupport_spatialSchwartzExponential
    (a : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (hφ : HasCompactSupport φ) (z : ℂ) :
    HasCompactSupport (spatialSchwartzExponential a φ hφ z) := by
  change HasCompactSupport (fun x => Complex.exp (z * (a x : ℂ)) * φ x)
  exact hφ.mul_left

theorem spatialSchwartzExponential_add
    (a : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (hφ : HasCompactSupport φ) (z₀ z : ℂ) :
    spatialSchwartzExponential a (spatialSchwartzExponential a φ hφ z₀)
      (hasCompactSupport_spatialSchwartzExponential a φ hφ z₀) z =
        spatialSchwartzExponential a φ hφ (z₀ + z) := by
  ext x
  simp only [spatialSchwartzExponential_apply, add_mul, Complex.exp_add]
  ring

private theorem compact_phase_bound
    (a : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (hφ : HasCompactSupport φ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ tsupport φ, |a x| ≤ R := by
  obtain ⟨C, hC⟩ := hφ.exists_bound_of_continuousOn a.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have hh : |a x| ≤ C := by simpa only [Real.norm_eq_abs] using hC x hx
  exact hh.trans (le_max_left _ _)

/-- The actual Taylor truncations converge in the genuine Schwartz topology. -/
theorem tendsto_spatialSchwartzExponential_partialSums
    (a : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (hφ : HasCompactSupport φ) (z : ℂ) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, z ^ n • spatialExponentialCoefficient a φ n)
      atTop (𝓝 (spatialSchwartzExponential a φ hφ z)) := by
  obtain ⟨R, hR, ha⟩ := compact_phase_bound a φ hφ
  let f : ℕ → SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ :=
    fun n => z ^ n • spatialExponentialCoefficient a φ n
  have hf : ∀ k j, Summable (fun n => SchwartzMap.seminorm ℂ k j (f n)) := by
    intro k j
    simpa only [f, map_smul_eq_mul, norm_pow] using
      summable_seminorm_spatialExponentialCoefficient a φ hR ha (norm_nonneg z) k j
  have heq : schwartzSeries f hf = spatialSchwartzExponential a φ hφ z := by
    ext x
    have ht := (NormedSpace.expSeries_div_hasSum_exp (z * (a x : ℂ))).mul_right (φ x)
    rw [← Complex.exp_eq_exp_ℂ] at ht
    have hterm (n : ℕ) : f n x = (z * (a x : ℂ)) ^ n / (n.factorial : ℂ) * φ x := by
      simp only [f, spatialExponentialCoefficient, smul_apply, spatialLinearMoment_apply,
        smul_eq_mul, Complex.real_smul, Complex.ofReal_pow, mul_pow]
      ring
    simpa only [schwartzSeries_apply, hterm, spatialSchwartzExponential_apply] using ht.tsum_eq
  simpa only [heq, f] using tendsto_schwartzSeries_partialSums f hf

/-- Scalar power series agree with actual evaluation, rather than merely defining an auxiliary
sum. -/
theorem hasSum_distribution_spatialSchwartzExponential
    (T : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ)
    (a : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (hφ : HasCompactSupport φ) (z : ℂ) :
    HasSum (fun n => z ^ n * T (spatialExponentialCoefficient a φ n))
      (T (spatialSchwartzExponential a φ hφ z)) := by
  obtain ⟨R, hR, ha⟩ := compact_phase_bound a φ hφ
  apply (summable_distribution_spatialExponentialCoefficient T a φ hR ha
    z).hasSum_iff_tendsto_nat.mpr
  have h := T.continuous.continuousAt.tendsto.comp
    (tendsto_spatialSchwartzExponential_partialSums a φ hφ z)
  change Tendsto (fun n => T.toLinearMap (∑ i ∈ Finset.range n,
    z ^ i • spatialExponentialCoefficient a φ i)) atTop
      (𝓝 (T (spatialSchwartzExponential a φ hφ z))) at h
  simp only [map_sum, map_smul, smul_eq_mul] at h
  convert h using 1; rfl

/-- Evaluating a compact cutoff exponential against an actual tempered distribution is entire. -/
theorem analyticOnNhd_distribution_spatialSchwartzExponential
    (T : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ)
    (a : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (hφ : HasCompactSupport φ) :
    AnalyticOnNhd ℂ (fun z => T (spatialSchwartzExponential a φ hφ z)) Set.univ := by
  intro z₀ hz₀
  let ψ := spatialSchwartzExponential a φ hφ z₀
  have hψ : HasCompactSupport ψ := hasCompactSupport_spatialSchwartzExponential a φ hφ z₀
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun n => T (spatialExponentialCoefficient a ψ n))
  apply HasFPowerSeriesAt.analyticAt (p := p)
  rw [hasFPowerSeriesAt_iff]
  apply Filter.Eventually.of_forall
  intro z
  have h := hasSum_distribution_spatialSchwartzExponential T a ψ hψ z
  simpa only [p, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul,
    ψ, spatialSchwartzExponential_add] using h

end VacuumBellSeparation
