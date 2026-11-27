/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! # A genuine uniform mixture on finitely tagged parameter spaces -/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped ENNReal

variable {I A B : Type*} [Fintype I] [MeasurableSpace I]
  [MeasurableSpace A] [MeasurableSpace B]

/-- Finite tagged probability given by `(Fintype.card I : ℝ≥0∞)⁻¹ • Measure.sum (fun i => (ν i).map
(Prod.mk i))`. -/
noncomputable def finiteTaggedProbability (ν : I → Measure A) : Measure (I × A) :=
  (Fintype.card I : ℝ≥0∞)⁻¹ • Measure.sum (fun i => (ν i).map (Prod.mk i))

instance finiteTaggedProbability_isProbability [Nonempty I]
    (ν : I → Measure A) [∀ i, IsProbabilityMeasure (ν i)] :
    IsProbabilityMeasure (finiteTaggedProbability ν) := by
  constructor
  have hN : (Fintype.card I : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [finiteTaggedProbability, smul_apply, smul_eq_mul,
    Measure.sum_apply _ MeasurableSet.univ, Measure.map_apply measurable_prodMk_left
      MeasurableSet.univ,
    Set.preimage_univ, measure_univ, tsum_fintype, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel hN (by simp)

theorem finiteTaggedProbability_ae (ν : I → Measure A) {P : I × A → Prop}
    (hP : MeasurableSet {x | P x}) (h : ∀ i, ∀ᵐ a ∂ν i, P (i, a)) :
    ∀ᵐ x ∂finiteTaggedProbability ν, P x := by
  apply Measure.ae_smul_measure
  apply Measure.ae_sum_iff.mpr
  intro i
  exact (ae_map_iff measurable_prodMk_left.aemeasurable hP).mpr (h i)

theorem finiteTaggedProbability_prod_lintegral (ν : I → Measure A)
    (μ : Measure B) [SFinite μ] {G : (I × A) × B → ℝ≥0∞} (hG : Measurable G) :
    (∫⁻ y, G y ∂(finiteTaggedProbability ν).prod μ) =
      (Fintype.card I : ℝ≥0∞)⁻¹ *
        ∑ i, ∫⁻ y : A × B, G ((i, y.1), y.2) ∂(ν i).prod μ := by
  rw [finiteTaggedProbability, Measure.prod_smul_left, lintegral_smul_measure,
    Measure.prod_sum_left, lintegral_sum_measure, tsum_fintype]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have he : ((ν i).map (Prod.mk i)).prod μ =
      ((ν i).prod μ).map (fun y : A × B => ((i, y.1), y.2)) := by
    simpa only [Prod.map_def, Function.id_def, Measure.map_id'] using
      Measure.map_prod_map (ν i) μ
        (measurable_prodMk_left : Measurable (Prod.mk i : A → I × A))
        (measurable_id : Measurable (id : B → B))
  rw [he, lintegral_map hG (by fun_prop)]

omit [MeasurableSpace I] in
/-- A finite cover costs only the uniform mixture weight and the minimum
of the local constants. Overlap causes no further loss. -/
theorem finite_union_lintegral_domination {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : I → Set X) (F : X → ℝ≥0∞)
    (c : I → ℝ≥0∞) (P : I → ℝ≥0∞) (a k : ℝ≥0∞)
    (hk : ∀ i, k ≤ c i)
    (h : ∀ i, c i * (∫⁻ x in S i, F x ∂μ) ≤ P i) :
    (a * k) * (∫⁻ x in ⋃ i, S i, F x ∂μ) ≤ a * ∑ i, P i := by
  have hu := lintegral_iUnion_le (μ := μ) S F
  rw [tsum_fintype] at hu
  calc
    _ = a * (k * (∫⁻ x in ⋃ i, S i, F x ∂μ)) := mul_assoc _ _ _
    _ ≤ a * (k * ∑ i, ∫⁻ x in S i, F x ∂μ) := mul_le_mul' le_rfl (mul_le_mul' le_rfl hu)
    _ = a * ∑ i, k * (∫⁻ x in S i, F x ∂μ) := by rw [Finset.mul_sum]
    _ ≤ a * ∑ i, P i := by
      apply mul_le_mul' le_rfl
      apply Finset.sum_le_sum
      intro i _
      exact (mul_le_mul' (hk i) le_rfl).trans (h i)

end VacuumBellSeparation
