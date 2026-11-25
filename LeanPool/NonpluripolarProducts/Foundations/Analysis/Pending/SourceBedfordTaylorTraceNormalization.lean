/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SourceBedfordTaylorCurrentNormalization

/-!
# Rescaling the trace measure

The trace of a positive current scales by the same nonnegative factor as
the current. For the auxiliary convention `D = 2π ddᶜ`, the trace of a
product of `q` factors therefore scales by `(2π)^q`.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.SourceBedfordTaylorTraceNormalization

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts SourceBedfordTaylorCurrentNormalization

variable {n : ℕ} {U : Opens (ComplexModel n)}

private theorem traceMeasureOn_smul {r : ℕ} {T : LocalProductCurrent n U r}
    (hT : IsPositive T) {c : ℝ} (hc : 0 ≤ c) :
    (hT.smul hc).traceMeasureOn = Real.toNNReal c • hT.traceMeasureOn := by
  let : hT.traceMeasureOn.Regular :=
    (Classical.choose_spec hT.positiveDistribution_trace.exists_regular_measure).1
  let : (hT.smul hc).traceMeasureOn.Regular :=
    (Classical.choose_spec (hT.smul hc).positiveDistribution_trace.exists_regular_measure).1
  let : IsLocallyFiniteMeasure hT.traceMeasureOn := hT.isLocallyFiniteMeasure_traceMeasureOn
  let : IsLocallyFiniteMeasure (hT.smul hc).traceMeasureOn :=
    (hT.smul hc).isLocallyFiniteMeasure_traceMeasureOn
  apply Pending.Measure.eq_of_testFunction_integral_eq
  intro φ
  rw [IsPositive.integral_traceMeasureOn, integral_smul_nnreal_measure,
    IsPositive.integral_traceMeasureOn, NNReal.smul_def, smul_eq_mul,
    Real.coe_toNNReal _ hc]
  rfl

/-- Actual Riesz trace measures commute with nonnegative scaling of the current. -/
theorem traceMeasure_smul {r : ℕ} {T : LocalProductCurrent n U r}
    (hT : IsPositive T) {c : ℝ} (hc : 0 ≤ c) :
    (hT.smul hc).traceMeasure = Real.toNNReal c • hT.traceMeasure := by
  change ((hT.smul hc).traceMeasureOn).map Subtype.val = _
  rw [traceMeasureOn_smul hT hc, Measure.map_smul _ measurable_subtype_coe.aemeasurable]
  rfl

/-- The trace of the product with `D = 2π ddᶜ` is scaled by `(2π)^q`. -/
theorem sourceDProduct_traceMeasure (q r : ℕ) (u : Fin q → ComplexModel n → ℝ)
    (T : LocalProductCurrent n U (r + q)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + q) T) (hu : ∀ i, IsLocallyBoundedPshOn U (u i)) :
    (sourceDProduct_positive_closed q r u T hT hTc hu).1.traceMeasure =
      Real.toNNReal ((2 * Real.pi) ^ q) • (isPositive_btProduct q r u T hT hTc hu).1.traceMeasure
        := by
  simpa only [sourceDProduct_eq q r u T hT hTc hu] using
    traceMeasure_smul (isPositive_btProduct q r u T hT hTc hu).1
      (show 0 ≤ (2 * Real.pi) ^ q by positivity)

end SGPT.Foundations.Analysis.Pending.SourceBedfordTaylorTraceNormalization
