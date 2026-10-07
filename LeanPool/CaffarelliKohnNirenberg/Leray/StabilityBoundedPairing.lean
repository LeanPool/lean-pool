/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityTestBounds

/-!
# Stability Bounded Pairing

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory
open scoped ENNReal
noncomputable section

namespace CKN

/-- On a finite-measure set, an `Lᵖ` field with `p ≥ 1` has an integrable
pairing with an essentially bounded scalar test. -/
theorem stability_integrable_mul_bounded_test
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {r : ℝ≥0∞} (hr : 1 ≤ r) {f φ : α → ℝ}
    (hf : MemLp f r μ) (hφ : MemLp φ ∞ μ) :
    Integrable (fun x => f x * φ x) μ := by
  have hfi : Integrable f μ :=
    memLp_one_iff_integrable.mp (hf.mono_exponent hr)
  have heq : (fun x => f x * φ x) = f * φ := by
    funext x
    rfl
  rw [heq]
  exact hfi.mul_of_top_left hφ

end CKN
