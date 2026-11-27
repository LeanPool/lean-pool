/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.DampedSpatialUnique
public import LeanPool.VacuumBellSeparation.FreeField.ScalarFourierInjectivity

/-!
# No nonzero physical complex annihilator of a nonempty time-zero ball

Actual bounded exponential damping produces a physical L² ∩ L¹ vector.
The proved spatial Fourier vanishing and distributional injectivity make
that vector zero. Strict positivity of the damping cancels almost everywhere;
there is no domain assertion for an exponentially growing inverse.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter
open scoped InnerProductSpace ComplexConjugate

theorem memLp_dampedShellAmplitude {m a : ℝ} (hm : 0 < m) (ha : 0 ≤ a)
    (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    MemLp (dampedShellAmplitude a ψ) 2 (oneParticleMeasure m) := by
  apply (Lp.memLp ψ).of_le
  · have hc : Continuous (fun p => (Real.exp (-a * dispersion m p) : ℂ)) :=
      Complex.continuous_ofReal.comp ((continuous_const.mul (continuous_dispersion m)).rexp)
    exact hc.aestronglyMeasurable.mul (Lp.memLp ψ).aestronglyMeasurable.star
  · exact Eventually.of_forall fun p => by
      rw [norm_dampedShellAmplitude]
      apply mul_le_of_le_one_left (norm_nonneg _)
      rw [Real.exp_le_one_iff]
      simpa only [neg_mul] using
        neg_nonpos.mpr (mul_nonneg ha (hm.le.trans (le_dispersion hm.le p)))

theorem eq_zero_of_dampedSpatialFourier_eq_zero {m a : ℝ}
    (hm : 0 < m) (ha : 0 < a) (ψ : Lp ℂ 2 (oneParticleMeasure m))
    (hzero : dampedSpatialFourier a ψ = 0) : ψ = 0 := by
  let u := (memLp_dampedShellAmplitude hm ha.le ψ).toLp (dampedShellAmplitude a ψ)
  have hcoe : (fun p => u p) =ᵐ[oneParticleMeasure m] dampedShellAmplitude a ψ :=
    (memLp_dampedShellAmplitude hm ha.le ψ).coeFn_toLp
  have hu : Integrable (fun p => u p) (oneParticleMeasure m) :=
    (integrable_dampedShellAmplitude hm ha ψ).congr hcoe.symm
  have hFu : scalarSpatialFourier (oneParticleMeasure m) (fun p => u p) = 0 := by
    calc
      _ = dampedSpatialFourier a ψ := by
        funext x
        apply integral_congr_ae
        exact hcoe.mono fun p hp => by
          dsimp only at hp ⊢
          rw [hp]
      _ = 0 := hzero
  have hu0 := physical_L2_eq_zero_of_scalarSpatialFourier_eq_zero hm u hu hFu
  have hA : dampedShellAmplitude a ψ =ᵐ[oneParticleMeasure m] 0 := by
    exact hcoe.symm.trans (by simpa only [hu0] using Lp.coeFn_zero ℂ 2 (oneParticleMeasure m))
  apply Lp.ext
  filter_upwards [hA, Lp.coeFn_zero ℂ 2 (oneParticleMeasure m)] with p hp hz
  rw [hz]
  have hexp : (Real.exp (-a * dispersion m p) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  change (Real.exp (-a * dispersion m p) : ℂ) * conj (ψ p) = 0 at hp
  have hconj : conj (ψ p) = 0 := (mul_eq_zero.mp hp).resolve_left hexp
  simpa using hconj

theorem eq_zero_of_local_timeZero_complex_annihilator {m R : ℝ}
    (hm : 0 < m) (hR : 0 < R) (x₀ : EuclideanSpace ℝ (Fin 3))
    (ψ : Lp ℂ 2 (oneParticleMeasure m))
    (hψ : ∀ u ∈ localizedTimeZeroSources (Metric.ball x₀ R),
      ⟪ψ, timeZeroL2 hm u⟫_ℂ = 0) : ψ = 0 := by
  apply eq_zero_of_dampedSpatialFourier_eq_zero hm (show (0 : ℝ) < 1 by norm_num) ψ
  exact dampedSpatialFourier_eq_zero_of_local_annihilator hm (by norm_num) hR x₀ ψ hψ

end VacuumBellSeparation
