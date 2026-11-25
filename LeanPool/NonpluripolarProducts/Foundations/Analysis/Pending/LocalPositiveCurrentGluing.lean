/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ScalarLeviPositiveCurrent
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorLocality

/-! # Full positivity of actual local product currents is local -/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending.LocalPositiveCurrentGluing

open FirstPass StronglyPositiveForms LocalProductCurrents LocalBedfordTaylorProducts
  LocalBedfordTaylorLocality ScalarLeviPositiveCurrent

variable {n : ℕ} {U V : Opens (ComplexModel n)}

/-- The actual scalar top current commutes with genuine open restriction. -/
theorem scalarTopCurrent_restrict (hVU : V ≤ U) (T : 𝓓'(U, ℝ)) :
    restrict hVU (scalarTopCurrent T) = scalarTopCurrent (restrictDistribution T hVU) := by
  ext γ φ
  rw [LocalBedfordTaylorLocality.restrict_apply, scalarTopCurrent_apply, scalarTopCurrent_apply,
    restrictDistribution_apply]
  rfl

/-- Restriction also commutes with the scalar top current's genuine differential. -/
theorem ddc_scalarTopCurrent_restrict
    {m : ℕ} {A B : Opens (ComplexModel (m + 1))} (hBA : B ≤ A) (T : 𝓓'(A, ℝ)) :
    restrict hBA (ddc (scalarTopCurrent T)) =
      ddc (scalarTopCurrent (restrictDistribution T hBA)) := by
  rw [← ddc_restrict, scalarTopCurrent_restrict]

/-- Scalar Levi positivity produces full current positivity on the entire actual open set. -/
theorem isPositive_ddc_scalarTopCurrent
    {m : ℕ} {A : Opens (ComplexModel (m + 1))} {T : 𝓓'(A, ℝ)}
    (hT : HasNonnegativeDistributionalLevi T) : IsPositive (ddc (scalarTopCurrent T)) := by
  apply isPositive_of_local_restrict
  intro x hx
  obtain ⟨B, hBA, hxB, hpos⟩ := exists_local_isPositive_ddc_scalarTopCurrent hT x hx
  exact ⟨B, hBA, hxB, by simpa only [ddc_scalarTopCurrent_restrict] using hpos⟩

end SGPT.Foundations.Analysis.Pending.LocalPositiveCurrentGluing
