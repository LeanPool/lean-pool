/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityS1LocalCore
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Stability Integral Convergence

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open scoped ENNReal
noncomputable section

namespace CKN

/-- On a finite-measure set, strong `L³` convergence implies convergence of
Bochner integrals. This is the linear limit step in (S2) and (S3) of
`thm:stability`. -/
theorem stability_tendsto_integral_of_Lthree
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) [IsFiniteMeasure μ]
    (F : ℕ → α → E) (G : α → E)
    (hF : ∀ n, MemLp (F n) 3 μ)
    (hconv : Tendsto (fun n => eLpNorm (F n - G) 3 μ) atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, F n x ∂μ) atTop (nhds (∫ x, G x ∂μ)) := by
  let C : ℝ≥0∞ := μ Set.univ ^ (2 / 3 : ℝ)
  have hC : C < ⊤ := by
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by finiteness)
  have hbound (n : ℕ) : eLpNorm (F n - G) 1 μ ≤
      eLpNorm (F n - G) 3 μ * C := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ_of_pos
      (f := F n - G) (μ := μ) (p := (1 : ℝ≥0∞)) (q := (3 : ℝ≥0∞))
      (by norm_num) (by norm_num)
    convert h using 1
    norm_num [C]
  have hmul : Tendsto (fun n => eLpNorm (F n - G) 3 μ * C)
      atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.mul_const hconv (Or.inr hC.ne)
  have hconv1 : Tendsto (fun n => eLpNorm (F n - G) 1 μ)
      atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmul
      (Filter.Eventually.of_forall fun _ => bot_le)
      (Filter.Eventually.of_forall hbound)
  have hF1 (n : ℕ) : MemLp (F n) 1 μ :=
    (hF n).mono_exponent (by norm_num)
  exact tendsto_integral_of_L1' G
    (Filter.Eventually.of_forall fun n => memLp_one_iff_integrable.mp (hF1 n)) hconv1

end CKN
