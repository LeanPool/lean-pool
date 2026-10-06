/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityFixedMultiplier
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Stability Component Convergence

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open scoped ENNReal
noncomputable section

namespace CKN

/-- Strong `L³` convergence of a finite vector field passes to each component
(`thm:stability`). -/
theorem stability_tendsto_eLpNorm_component_three
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {ι : Type*} [Fintype ι]
    (F : ℕ → α → ι → ℝ) (G : α → ι → ℝ)
    (hF : ∀ n, MemLp (F n) 3 μ)
    (hconv : Tendsto (fun n => eLpNorm (F n - G) 3 μ) atTop (nhds 0))
    (i : ι) :
    Tendsto (fun n => eLpNorm (fun x => F n x i - G x i) 3 μ)
      atTop (nhds 0) := by
  have hG : MemLp G 3 μ :=
    Lp.memLp_of_cauchy_tendsto (by norm_num) hF G hconv
  have hle (n : ℕ) :
      eLpNorm (fun x => F n x i - G x i) 3 μ ≤ eLpNorm (F n - G) 3 μ := by
    have hdiff : MemLp (F n - G) 3 μ := (hF n).sub hG
    have hcomponent : AEStronglyMeasurable
        (fun x => (F n x - G x) i) μ :=
      (continuous_apply i).comp_aestronglyMeasurable hdiff.aestronglyMeasurable
    have h := eLpNorm_mono_ae (p := (3 : ℝ≥0∞)) hcomponent
      (Filter.Eventually.of_forall fun x => norm_le_pi_norm (F n x - G x) i)
    change eLpNorm (fun x => F n x i - G x i) 3 μ ≤
      eLpNorm (fun x => F n x - G x) 3 μ
    simpa only [Pi.sub_apply] using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hconv
    (Filter.Eventually.of_forall fun _ => bot_le)
    (Filter.Eventually.of_forall hle)

end CKN
