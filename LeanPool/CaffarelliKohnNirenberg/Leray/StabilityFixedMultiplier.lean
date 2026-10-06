/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityIntegralConvergence

/-!
# Stability Fixed Multiplier

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open scoped ENNReal
noncomputable section

namespace CKN

/-- A fixed essentially bounded scalar test preserves convergence of the
integrals of a strongly `L³`-convergent sequence (`thm:stability`). -/
theorem stability_tendsto_integral_mul_test_of_Lthree
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) [IsFiniteMeasure μ]
    (F : ℕ → α → E) (G : α → E) (φ : α → ℝ)
    (hF : ∀ n, MemLp (F n) 3 μ)
    (hφ : MemLp φ ∞ μ)
    (hconv : Tendsto (fun n => eLpNorm (F n - G) 3 μ) atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, φ x • F n x ∂μ) atTop
      (nhds (∫ x, φ x • G x ∂μ)) := by
  have hG : MemLp G 3 μ := Lp.memLp_of_cauchy_tendsto
    (by norm_num) hF G hconv
  have hscaled (n : ℕ) : eLpNorm (fun x => φ x • F n x - φ x • G x) 3 μ ≤
      eLpNorm φ ∞ μ * eLpNorm (F n - G) 3 μ := by
    have h := eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm
      (φ := φ) (f := F n - G) 3 hφ.aestronglyMeasurable
    have heq : (fun x => φ x • F n x - φ x • G x) = φ • (F n - G) := by
      funext x
      change φ x • F n x - φ x • G x = φ x • (F n x - G x)
      exact (smul_sub (φ x) (F n x) (G x)).symm
    rw [heq]
    exact h
  have hmul : Tendsto (fun n => eLpNorm φ ∞ μ * eLpNorm (F n - G) 3 μ)
      atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul hconv (Or.inr hφ.eLpNorm_ne_top)
  have hconvScaled : Tendsto
      (fun n => eLpNorm (fun x => φ x • F n x - φ x • G x) 3 μ)
      atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmul
      (Filter.Eventually.of_forall fun _ => bot_le)
      (Filter.Eventually.of_forall hscaled)
  have hFscaled (n : ℕ) : MemLp (fun x => φ x • F n x) 3 μ :=
    hφ.smul (hF n)
  exact stability_tendsto_integral_of_Lthree μ
    (fun n x => φ x • F n x) (fun x => φ x • G x)
    hFscaled hconvScaled

end CKN
