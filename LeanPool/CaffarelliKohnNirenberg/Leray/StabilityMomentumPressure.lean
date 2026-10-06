/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityMomentumViscous
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityPressureFixedMultiplier

/-!
# Stability Momentum Pressure

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- The pressure pairing in (S3) passes through strong local `L³ᐟ²`
convergence. -/
theorem stability_momentum_pressureTerm_tendsto
    {Ω Ω' : Set Vec3} {I J : Set ℝ} {q : ℝ}
    (u : ℕ → ParabolicPoint → Vec3)
    (Du : ℕ → ParabolicPoint → Fin 3 → Vec3)
    (p : ℕ → ParabolicPoint → ℝ)
    (r : ParabolicPoint → ℝ)
    (hsol : ∀ n, IsSuitableWeakSolution Ω I q (u n) (Du n) (p n) 0)
    (hbox : localBox Ω I Ω' J)
    (hpConv : Tendsto (fun n => eLpNorm (p n - r) (3 / 2 : ℝ≥0∞)
      (volume.restrict (spaceTimeSet Ω' J))) atTop (nhds 0))
    (φ : Vec3 × ℝ → Vec3)
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) Ω I) :
    Tendsto (fun n => ∫ z in spaceTimeSet Ω' J,
      p n z * ∑ i : Fin 3, spatialPartial (fun w => φ w i) i z) atTop
      (nhds (∫ z in spaceTimeSet Ω' J,
        r z * ∑ i : Fin 3, spatialPartial (fun w => φ w i) i z)) := by
  let μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet Ω' J)
  let _ : IsFiniteMeasure μ := stability_localBox_finiteMeasure hbox
  have hpN (n : ℕ) : MemLp (p n) (3 / 2 : ℝ≥0∞) μ := by
    have hdata := (isSuitableWeakSolution_iff_integrable.mp (hsol n)).toData
    simpa only [CKN.ofReal_threeHalves] using hdata.memLp_pressure hbox
  have h := stability_tendsto_integral_mul_test_of_LthreeHalves μ
    p r (fun z => ∑ i : Fin 3, spatialPartial (fun w => φ w i) i z)
    hpN (stability_testDivergence_memLp_top φ hφ) hpConv
  have heqFn (n : ℕ) :
      (∫ z, (∑ i : Fin 3, spatialPartial (fun w => φ w i) i z) * p n z ∂μ) =
        ∫ z, p n z * ∑ i : Fin 3, spatialPartial (fun w => φ w i) i z ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with z
    ring
  have heqG :
      (∫ z, (∑ i : Fin 3, spatialPartial (fun w => φ w i) i z) * r z ∂μ) =
        ∫ z, r z * ∑ i : Fin 3, spatialPartial (fun w => φ w i) i z ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with z
    ring
  simpa only [heqFn, heqG] using h

end CKN
