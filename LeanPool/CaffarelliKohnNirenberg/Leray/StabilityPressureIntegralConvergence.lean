/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityIntegralConvergence
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.VelocityTenThirds

/-!
# Stability Pressure Integral Convergence

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open scoped ENNReal
noncomputable section

namespace CKN

/-- On a finite-measure set, strong `L^{3/2}` convergence passes to scalar
integrals. -/
theorem stability_tendsto_integral_of_LthreeHalves
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (F : ℕ → α → ℝ) (G : α → ℝ)
    (hF : ∀ n, MemLp (F n) (3 / 2 : ℝ≥0∞) μ)
    (hconv : Tendsto (fun n => eLpNorm (F n - G) (3 / 2 : ℝ≥0∞) μ)
      atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, F n x ∂μ) atTop (nhds (∫ x, G x ∂μ)) := by
  let C : ℝ≥0∞ := μ Set.univ ^ (1 / 3 : ℝ)
  have hOne : (1 : ℝ≥0∞) ≤ (3 / 2 : ℝ≥0∞) := by
    rw [← CKN.ofReal_threeHalves]
    simpa using ENNReal.ofReal_le_ofReal (by norm_num : (1 : ℝ) ≤ 3 / 2)
  have hC : C < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by finiteness)
  have hbound (n : ℕ) : eLpNorm (F n - G) 1 μ ≤
      eLpNorm (F n - G) (3 / 2 : ℝ≥0∞) μ * C := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ_of_pos
      (f := F n - G) (μ := μ) (p := (1 : ℝ≥0∞))
      (q := (3 / 2 : ℝ≥0∞)) hOne (by norm_num)
    convert h using 1
    norm_num [C]
  have hmul : Tendsto
      (fun n => eLpNorm (F n - G) (3 / 2 : ℝ≥0∞) μ * C)
      atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.mul_const hconv (Or.inr hC.ne)
  have hconv1 : Tendsto (fun n => eLpNorm (F n - G) 1 μ)
      atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmul
      (Filter.Eventually.of_forall fun _ => bot_le)
      (Filter.Eventually.of_forall hbound)
  have hF1 (n : ℕ) : MemLp (F n) 1 μ :=
    (hF n).mono_exponent hOne
  exact tendsto_integral_of_L1' G
    (Filter.Eventually.of_forall fun n => memLp_one_iff_integrable.mp (hF1 n)) hconv1

end CKN
