/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Conditional expectation onto the σ-algebra of a countable partition

Let `φ : α → ι` take values in a countable type and have measurable fibres `φ⁻¹{i}`.  The
σ-algebra `MeasurableSpace.comap φ ⊤` consists of the unions of fibres: it is the σ-algebra of
the partition of `α` into the fibres of `φ`.  For a finite measure the conditional expectation
onto it is the average over the cell (`MeasureTheory.condExp_comap_ae_eq`):

`E[f | φ](x) = μ(φ⁻¹{φ x})⁻¹ ∫_{φ⁻¹{φ x}} f dμ`   for almost every `x`.

The dyadic σ-algebras of the Haar system are of this form, with `φ(x) = ⌊2^j x⌋`.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory

variable {α ι E : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The σ-algebra of the fibres of `φ` lies below the ambient σ-algebra when the fibres are
measurable and `φ` takes countably many values. -/
theorem comap_top_le [Countable ι] {φ : α → ι} (hφ : ∀ i, MeasurableSet (φ ⁻¹' {i})) :
    MeasurableSpace.comap φ ⊤ ≤ m0 := by
  rintro s ⟨T, -, rfl⟩
  rw [← Set.biUnion_preimage_singleton]
  exact MeasurableSet.biUnion T.to_countable fun i _ => hφ i

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- A function measurable for the σ-algebra of the fibres of `φ` is constant on every fibre. -/
theorem StronglyMeasurable.eq_of_comap_top [MeasurableSpace E] [BorelSpace E] {φ : α → ι}
    {g : α → E} (hg : StronglyMeasurable[MeasurableSpace.comap φ ⊤] g) {x y : α}
    (hxy : φ y = φ x) : g y = g x := by
  obtain ⟨T, -, hT⟩ := MeasurableSpace.measurableSet_comap.1
    (hg.measurable (measurableSet_singleton (g x)))
  have hx : x ∈ φ ⁻¹' T := by rw [hT]; rfl
  have hy : y ∈ φ ⁻¹' T := by rw [Set.mem_preimage, hxy]; exact hx
  rw [hT] at hy
  exact hy

/-- **Conditional expectation onto a countable partition**: for a finite measure and an
integrable `f`, `E[f | φ](x)` is the average of `f` over the fibre of `φ` through `x`, for
almost every `x`.  The fibres of measure `0` form a null set, which is why the formula holds
only almost everywhere. -/
theorem condExp_comap_ae_eq [Countable ι] [IsFiniteMeasure μ] [MeasurableSpace E] [BorelSpace E]
    {φ : α → ι} (hφ : ∀ i, MeasurableSet (φ ⁻¹' {i})) {f : α → E} (hf : Integrable f μ) :
    μ[f | MeasurableSpace.comap φ ⊤] =ᵐ[μ]
      fun x => (μ.real (φ ⁻¹' {φ x}))⁻¹ • ∫ y in φ ⁻¹' {φ x}, f y ∂μ := by
  have hm : MeasurableSpace.comap φ ⊤ ≤ m0 := comap_top_le hφ
  have hg : StronglyMeasurable[MeasurableSpace.comap φ ⊤] (μ[f | MeasurableSpace.comap φ ⊤]) :=
    stronglyMeasurable_condExp
  have hnull : ∀ᵐ x ∂μ, μ (φ ⁻¹' {φ x}) ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not]
    refine measure_mono_null (t := ⋃ i ∈ {i | μ (φ ⁻¹' {i}) = 0}, φ ⁻¹' {i}) ?_
      ((measure_biUnion_null_iff (Set.to_countable _)).2 fun i hi => hi)
    intro x hx
    simp only [Set.mem_iUnion]
    exact ⟨φ x, hx, rfl⟩
  filter_upwards [hnull] with x hx
  have hfib : MeasurableSet[MeasurableSpace.comap φ ⊤] (φ ⁻¹' {φ x}) := ⟨{φ x}, trivial, rfl⟩
  have hint := setIntegral_condExp hm hf hfib
  have hconst : ∫ y in φ ⁻¹' {φ x}, (μ[f | MeasurableSpace.comap φ ⊤]) y ∂μ =
      μ.real (φ ⁻¹' {φ x}) • (μ[f | MeasurableSpace.comap φ ⊤]) x := by
    rw [← setIntegral_const]
    exact setIntegral_congr_fun (hφ (φ x)) fun y hy => hg.eq_of_comap_top hy
  have hreal : μ.real (φ ⁻¹' {φ x}) ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨hx, measure_ne_top μ _⟩
  rw [← hint, hconst, smul_smul, inv_mul_cancel₀ hreal, one_smul]

end MeasureTheory
