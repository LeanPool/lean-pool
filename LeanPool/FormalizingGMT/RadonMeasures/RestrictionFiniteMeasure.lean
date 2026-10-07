/-
Copyright (c) 2026 FormalizingGMT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalizingGMT contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.Metrizable.Urysohn

/-!
# Regularity and approximation for restrictions of finite measure

This file proves regularity of a measure restricted to a set of finite measure, together with
closed inner approximations and open outer approximations of Carathéodory-measurable sets.
-/

@[expose] public section

open scoped BigOperators ENNReal

open MeasureTheory Set

/-! ## Regularity of the restriction of a measure to a set of finite measure -/

section MeasureRestrict

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X] {μ : Measure X}

/-- **Restriction of a measure to a set of finite measure is regular.**
Let `X` be a locally compact, Hausdorff, second countable topological space equipped with its
Borel σ-algebra, let `μ` be a measure on `X`, and let `E ⊆ X` satisfy `μ E < ∞`.  Then the
restriction `μ.restrict E` belongs to Mathlib's class `MeasureTheory.Measure.Regular`, i.e. it is
outer regular by open sets and inner regular by compact sets on open (indeed, on finite-measure
measurable) sets. -/
theorem BorelRegularOuterMeasure.restrict_isRadon
    [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X]
    (E : Set X) (hE_fin : μ E < ⊤) :
    (μ.restrict E).Regular := by
  let _ : IsFiniteMeasure (μ.restrict E) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simpa using hE_fin⟩
  let _ : TopologicalSpace.MetrizableSpace X :=
    TopologicalSpace.metrizableSpace_of_t3_secondCountable X
  infer_instance

end MeasureRestrict

/-! ## Approximation results for measures on a locally compact, second countable Borel space -/

section MeasureApproximation

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
  [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X]

/-- **Approximation of Carathéodory-measurable sets of finite measure by closed sets from
inside.**  Let `X` be a locally compact, Hausdorff, second countable topological space equipped
with its Borel σ-algebra and let `μ` be a measure on `X` (so that `μ`, viewed as an outer
measure, is Borel regular).  If `E ⊆ X` is Carathéodory measurable for `μ` with `μ E < ∞` and
`ε > 0`, then there is a closed set `F ⊆ E` with `μ (E \ F) < ε`.

Reference: Mattila's book, Theorem 1.10 (1), page 11. -/
theorem closed_approx_of_isBorelRegular
    (μ : Measure X) (E : Set X) (hE : μ.toOuterMeasure.IsCaratheodory E)
    (hEfin : μ E < ∞) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ F : Set X, IsClosed F ∧ F ⊆ E ∧ μ (E \ F) < ε := by
  -- Choose a measurable superset `B ⊇ E` of the same measure.
  obtain ⟨B, hEB, hB_meas, hB_eq⟩ := exists_measurable_superset μ E
  -- Carathéodory measurability of `E`, tested against `B`, shows that `B \ E` is null.
  have hBE_null : μ (B \ E) = 0 := by
    have hcar := hE B
    simp only [Measure.toOuterMeasure_apply] at hcar
    rw [Set.inter_eq_self_of_subset_right hEB, hB_eq] at hcar
    exact ((ENNReal.add_right_inj hEfin.ne).1 (by simpa using hcar)).symm
  obtain ⟨N, hBEN, hN_meas, hN_null⟩ := exists_measurable_superset_of_null hBE_null
  -- `A = B \ N` is a measurable subset of `E` that exhausts `E` up to a null set.
  set A : Set X := B \ N with hA_def
  have hA_meas : MeasurableSet A := hB_meas.diff hN_meas
  have hAE : A ⊆ E := by
    rintro x ⟨hxB, hxN⟩
    by_contra hxE
    exact hxN (hBEN ⟨hxB, hxE⟩)
  -- The restriction of `μ` to `B` is a regular measure, since `μ B = μ E < ∞`.
  have hB_fin : μ B < ⊤ := hB_eq ▸ hEfin
  let _ : (μ.restrict B).Regular := BorelRegularOuterMeasure.restrict_isRadon B hB_fin
  -- Inner regularity by closed sets for `μ.restrict B`, applied to `A`.
  have hA_restrict_ne_top : (μ.restrict B) A ≠ ⊤ := by
    rw [Measure.restrict_apply hA_meas]
    exact ne_top_of_le_ne_top hB_fin.ne (measure_mono Set.inter_subset_right)
  obtain ⟨F, hFA, hF_closed, hF_lt⟩ :=
    hA_meas.exists_isClosed_sdiff_lt (μ := μ.restrict B) hA_restrict_ne_top hε.ne'
  refine ⟨F, hF_closed, hFA.trans hAE, ?_⟩
  -- Transfer the estimate back to `μ`, then add the null set `N`.
  have hAF : μ (A \ F) < ε := by
    have hmeas : MeasurableSet (A \ F) := hA_meas.diff hF_closed.measurableSet
    rwa [Measure.restrict_apply hmeas,
      Set.inter_eq_self_of_subset_left (Set.sdiff_subset.trans Set.sdiff_subset)] at hF_lt
  have hsub : E \ F ⊆ (A \ F) ∪ N := by
    rintro x ⟨hxE, hxF⟩
    by_cases hxN : x ∈ N
    · exact Or.inr hxN
    · exact Or.inl ⟨⟨hEB hxE, hxN⟩, hxF⟩
  calc μ (E \ F) ≤ μ ((A \ F) ∪ N) := measure_mono hsub
    _ ≤ μ (A \ F) + μ N := measure_union_le _ _
    _ < ε := by rw [hN_null, add_zero]; exact hAF

/- **Note.** The result below is purely instructional: it is not used anywhere else in the
project. -/

/-- **Approximation of Carathéodory-measurable sets by open sets from outside.**
Let `X` be a locally compact, Hausdorff, second countable topological space equipped with its
Borel σ-algebra and let `μ` be a measure on `X`.  Let `E ⊆ X` be Carathéodory measurable for `μ`
with `μ E < ∞` and let `ε > 0`.  If there are open sets `V i` with `E ⊆ ⋃ i, V i` and
`μ (V i) < ∞` for all `i`, then there is an open set `F ⊇ E` with `μ (F \ E) < ε`.

Reference: Mattila's book, Theorem 1.10 (2), page 11. -/
theorem open_approx_of_isBorelRegular
    (μ : Measure X) (E : Set X) (hE : μ.toOuterMeasure.IsCaratheodory E)
    (_hEfin : μ E < ∞)
    (V : ℕ → Set X) (hV_open : ∀ i, IsOpen (V i))
    (hEV : E ⊆ ⋃ i, V i) (hVfin : ∀ i, μ (V i) < ∞)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ F : Set X, IsOpen F ∧ E ⊆ F ∧ μ (F \ E) < ε := by
  obtain ⟨δ, hδpos, hδsum⟩ : ∃ δ : ℕ → ℝ≥0∞, (∀ i, 0 < δ i) ∧ (∑' i, δ i < ε) :=
    ENNReal.exists_pos_sum_of_countable' hε.ne' ℕ
  -- For each `i` the restriction of `μ` to `V i` is regular, hence outer regular.
  have key : ∀ i, ∃ U : Set X, IsOpen U ∧ E ∩ V i ⊆ U ∧ μ ((U ∩ V i) \ E) < δ i := by
    intro i
    let _ : (μ.restrict (V i)).Regular :=
      BorelRegularOuterMeasure.restrict_isRadon (V i) (hVfin i)
    have hfin : (μ.restrict (V i)) (E ∩ V i) ≠ ⊤ := by
      rw [Measure.restrict_apply' (hV_open i).measurableSet]
      exact ne_top_of_le_ne_top (hVfin i).ne (measure_mono Set.inter_subset_right)
    obtain ⟨U, hEU, hU_open, hU_lt⟩ :=
      Set.exists_isOpen_lt_add (μ := μ.restrict (V i)) (E ∩ V i) hfin (hδpos i).ne'
    refine ⟨U, hU_open, hEU, ?_⟩
    -- Rewrite the two sides of the outer-regularity estimate in terms of `μ`.
    have hEVU : (μ.restrict (V i)) (E ∩ V i) = μ ((U ∩ V i) ∩ E) := by
      rw [Measure.restrict_apply' (hV_open i).measurableSet]
      congr 1
      ext x
      simp only [mem_inter_iff]
      aesop
    have hUV : (μ.restrict (V i)) U = μ (U ∩ V i) := by
      rw [Measure.restrict_apply' (hV_open i).measurableSet]
    -- Carathéodory measurability of `E`, tested against `U ∩ V i`.
    have hcar := hE (U ∩ V i)
    simp only [Measure.toOuterMeasure_apply] at hcar
    rw [hEVU, hUV, hcar] at hU_lt
    have hfin' : μ ((U ∩ V i) ∩ E) ≠ ⊤ :=
      ne_top_of_le_ne_top (hVfin i).ne
        (measure_mono (fun _ hx => hx.1.2))
    exact (ENNReal.add_lt_add_iff_left hfin').1 hU_lt
  choose U hU_open hEU hU_lt using key
  refine ⟨⋃ i, U i ∩ V i, isOpen_iUnion fun i => (hU_open i).inter (hV_open i), ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hEV hx)
    exact mem_iUnion.2 ⟨i, hEU i ⟨hx, hi⟩, hi⟩
  · have hsub : (⋃ i, U i ∩ V i) \ E ⊆ ⋃ i, (U i ∩ V i) \ E := by simp [iUnion_sdiff]
    calc μ ((⋃ i, U i ∩ V i) \ E) ≤ μ (⋃ i, (U i ∩ V i) \ E) := measure_mono hsub
      _ ≤ ∑' i, μ ((U i ∩ V i) \ E) := measure_iUnion_le _
      _ ≤ ∑' i, δ i := ENNReal.tsum_le_tsum fun i => (hU_lt i).le
      _ < ε := hδsum

end MeasureApproximation
