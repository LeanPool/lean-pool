/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityWeightedGradientScalar

/-!
# Stability Weighted Product Integrable

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory
open scoped ENNReal
noncomputable section

namespace CKN

/-- The product of two `L²` fields, weighted by a bounded scalar function,
is integrable. -/
theorem stability_weighted_product_integrable
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {f g ψ : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hψ : MemLp ψ ∞ μ) :
    Integrable (fun x => f x * g x * ψ x) μ := by
  have hfg : MemLp (fun x => f x * g x) 1 μ := by
    have h : MemLp (f * g) 1 μ := hf.mul hg
    have heq : f * g = (fun x => f x * g x) := by funext x; rfl
    rwa [heq] at h
  exact stability_integrable_mul_bounded_test μ (by norm_num) hfg hψ

end CKN
