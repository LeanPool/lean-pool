/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
module

public import LeanPool.KLS.BrownianMotion.StochasticIntegral.SimpleProcess
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Notation

/-! # Real quasimartingales -/

@[expose] public section

open MeasureTheory
open scoped Function ProbabilityTheory.SimpleProcess

namespace ProbabilityTheory

variable {ι Ω : Type*} [LinearOrder ι] [OrderBot ι]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω}
  {X : ι → Ω → ℝ}

/-! ### Almost-sure regularity along countable time sets -/

-- todo: to be superceded by a more general `IsQuasimartingale`
/-- A real quasimartingale is a real-valued stochastic process that is adapted, integrable,
and has bounded variation. -/
structure IsRealQuasimartingale (𝓕 : Filtration ι mΩ) (X : ι → Ω → ℝ) (μ : Measure Ω) : Prop where
  adapted : Adapted 𝓕 X
  integrable : ∀ t, Integrable (X t) μ
  boundedVariation :
    ∀ t, ∃ C, ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C

/-- The minimal bound on the variation of the process. -/
noncomputable
def variationBound (X : ι → Ω → ℝ) (𝓕 : Filtration ι mΩ) (μ : Measure Ω) (t : ι) : ℝ :=
  ⨆ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t]

lemma IsRealQuasimartingale.integral_indicator_le_variationBound (hX : IsRealQuasimartingale 𝓕 X μ)
    (t : ι) (S : ElementaryPredictableSet 𝓕) :
    μ[(S.indicator (1 : ℝ) ● X) t] ≤ variationBound X 𝓕 μ t := by
  unfold variationBound
  refine le_ciSup (f := fun S ↦ ∫ x, (S.indicator 1 ● X) t x ∂μ) ?_ S
  obtain ⟨C, hC⟩ := hX.boundedVariation t
  exact ⟨C, by simp [mem_upperBounds, hC]⟩

lemma IsRealQuasimartingale.stronglyAdapted (hX : IsRealQuasimartingale 𝓕 X μ) :
    StronglyAdapted 𝓕 X := hX.adapted.stronglyAdapted

lemma IsRealQuasimartingale.measurable (hX : IsRealQuasimartingale 𝓕 X μ) (t : ι) :
    Measurable (X t) := (hX.adapted t).mono (𝓕.le t) le_rfl

/-! ### Martingales and submartingales are quasimartingales -/

/-- The elementary stochastic integral of the indicator of an elementary predictable set against a
martingale has zero expectation. -/
lemma _root_.MeasureTheory.Martingale.integral_elementaryPredictableSet_indicator_eq_zero
    [SigmaFiniteFiltration μ 𝓕] (hX : Martingale X 𝓕 μ) (S : ElementaryPredictableSet 𝓕) (t : ι) :
    μ[(S.indicator (1 : ℝ) ● X) t] = 0 := by
  rw [ElementaryPredictableSet.integral_integral_indicator_one hX.integrable]
  refine Finset.sum_eq_zero fun p hp ↦ ?_
  rcases le_or_gt p.1 t with hpt | hpt
  · have hA : MeasurableSet[𝓕 (min p.1 t)] (S.set p) := by
      rw [min_eq_left hpt]
      exact S.measurableSet_set p hp
    rw [integral_sub (hX.integrable _).integrableOn (hX.integrable _).integrableOn, sub_eq_zero]
    exact (hX.setIntegral_eq (min_le_min_right t (S.le_of_mem_I p hp)) hA).symm
  · simp [min_eq_right hpt.le, min_eq_right (hpt.le.trans (S.le_of_mem_I p hp))]

lemma _root_.MeasureTheory.Martingale.isRealQuasimartingale [SigmaFiniteFiltration μ 𝓕]
    (hX : Martingale X 𝓕 μ) :
    IsRealQuasimartingale 𝓕 X μ :=
  ⟨hX.stronglyAdapted.adapted, hX.integrable,
    fun t ↦ ⟨0, fun S ↦ (hX.integral_elementaryPredictableSet_indicator_eq_zero S t).le⟩⟩

omit [OrderBot ι] in
/-- For a submartingale `X`, times `s ≤ t` and a set `B ∈ 𝓕 s`, the expectation of the increment
`X t - X s` over `B` is at most the expectation of the increment. -/
lemma _root_.MeasureTheory.Submartingale.setIntegral_sub_setIntegral_le
    [SigmaFiniteFiltration μ 𝓕] (hX : Submartingale X 𝓕 μ) {s t : ι} (hst : s ≤ t) {B : Set Ω}
    (hB : MeasurableSet[𝓕 s] B) :
    ∫ ω in B, X t ω ∂μ - ∫ ω in B, X s ω ∂μ ≤ μ[X t] - μ[X s] := by
  have h1 := integral_add_compl (𝓕.le _ _ hB) (hX.integrable t)
  have h2 := integral_add_compl (𝓕.le _ _ hB) (hX.integrable s)
  have h3 := hX.setIntegral_le hst hB.compl
  linarith

/-- Auxiliary lemma for `Submartingale.integral_elementaryPredictableSet_indicator_le`, stated in
terms of the data of an elementary predictable set to allow for an induction on the set of
intervals. -/
lemma _root_.MeasureTheory.Submartingale.sum_setIntegral_sub_le_aux
    [SigmaFiniteFiltration μ 𝓕] (hX : Submartingale X 𝓕 μ) (A : ι × ι → Set Ω)
    (I : Finset (ι × ι)) :
    ∀ t, (∀ p ∈ I, p.1 ≤ p.2) → (∀ p ∈ I, MeasurableSet[𝓕 p.1] (A p)) →
      Set.PairwiseDisjoint ↑I (fun p : ι × ι ↦ Set.Ioc p.1 p.2 ×ˢ A p) →
      ∑ p ∈ I, (∫ ω in A p, X (min p.2 t) ω ∂μ - ∫ ω in A p, X (min p.1 t) ω ∂μ)
        ≤ μ[X t] - μ[X ⊥] := by
  classical
  induction I using Finset.induction_on_max_value (fun p : ι × ι ↦ p.1) with
  | empty =>
    intro t _ _ _
    have h := hX.setIntegral_le (bot_le : ⊥ ≤ t) MeasurableSet.univ
    simpa using h
  | insert q I hqI hq_max ih =>
    intro t hle hA hdisj
    set s := q.1 with hs
    have hle_s : ∀ p ∈ insert q I, p.1 ≤ s := by
      intro p hp
      rcases Finset.mem_insert.1 hp with rfl | hp
      · exact le_rfl
      · exact hq_max p hp
    -- the part of the sum before time `s`
    have h_before : ∑ p ∈ insert q I, (∫ ω in A p, X (min p.2 (min s t)) ω ∂μ
        - ∫ ω in A p, X (min p.1 (min s t)) ω ∂μ) ≤ μ[X (min s t)] - μ[X ⊥] := by
      rw [Finset.sum_insert hqI]
      have hq0 : ∫ ω in A q, X (min q.2 (min s t)) ω ∂μ
          - ∫ ω in A q, X (min q.1 (min s t)) ω ∂μ = 0 := by
        have hq2 : min q.2 (min s t) = min q.1 (min s t) := by
          rw [← min_assoc, ← min_assoc, min_eq_right (hle q (Finset.mem_insert_self q I)),
            min_self]
        rw [hq2, sub_self]
      rw [hq0, zero_add]
      exact ih (min s t) (fun p hp ↦ hle p (Finset.mem_insert_of_mem hp))
        (fun p hp ↦ hA p (Finset.mem_insert_of_mem hp))
        (hdisj.subset (by simp))
    -- the part of the sum after time `s`
    have h_after : ∑ p ∈ insert q I, (∫ ω in A p, X (min p.2 t) ω ∂μ
        - ∫ ω in A p, X (min p.2 (min s t)) ω ∂μ) ≤ μ[X t] - μ[X (min s t)] := by
      rcases le_total t s with hts | hst
      · simp [min_eq_right hts]
      rw [min_eq_left hst]
      let J := (insert q I).filter (fun p ↦ s < p.2)
      have hJ_sub : J ⊆ insert q I := Finset.filter_subset _ _
      have hJ_meas : ∀ p ∈ J, MeasurableSet[𝓕 s] (A p) :=
        fun p hp ↦ 𝓕.mono (hle_s p (hJ_sub hp)) _ (hA p (hJ_sub hp))
      have hJ_disj : Set.Pairwise (↑J) (Disjoint on A) := by
        intro p hp p' hp' hpp'
        have hpJ := Finset.mem_filter.1 hp
        have hpJ' := Finset.mem_filter.1 hp'
        have h := hdisj hpJ.1 hpJ'.1 hpp'
        simp only [Function.onFun, Set.disjoint_prod] at h ⊢
        refine h.resolve_left ?_
        rw [Set.not_disjoint_iff]
        refine ⟨min p.2 p'.2, ⟨?_, min_le_left _ _⟩, ⟨?_, min_le_right _ _⟩⟩
        · exact (hle_s p hpJ.1).trans_lt (lt_min hpJ.2 hpJ'.2)
        · exact (hle_s p' hpJ'.1).trans_lt (lt_min hpJ.2 hpJ'.2)
      calc ∑ p ∈ insert q I, (∫ ω in A p, X (min p.2 t) ω ∂μ - ∫ ω in A p, X (min p.2 s) ω ∂μ)
      _ ≤ ∑ p ∈ J, (∫ ω in A p, X t ω ∂μ - ∫ ω in A p, X s ω ∂μ) := by
        rw [Finset.sum_filter]
        refine Finset.sum_le_sum fun p hp ↦ ?_
        split_ifs with hsp
        · rw [min_eq_right hsp.le]
          refine sub_le_sub_right (hX.setIntegral_le (min_le_right _ _) ?_) _
          exact 𝓕.mono (le_min (hle p hp) ((hle_s p hp).trans hst)) _ (hA p hp)
        · rw [min_eq_left ((not_lt.1 hsp).trans hst), min_eq_left (not_lt.1 hsp), sub_self]
      _ = ∫ ω in ⋃ p ∈ J, A p, X t ω ∂μ - ∫ ω in ⋃ p ∈ J, A p, X s ω ∂μ := by
        rw [Finset.sum_sub_distrib,
          integral_biUnion_finset J (fun p hp ↦ 𝓕.le _ _ (hJ_meas p hp)) hJ_disj
            (fun _ _ ↦ (hX.integrable t).integrableOn),
          integral_biUnion_finset J (fun p hp ↦ 𝓕.le _ _ (hJ_meas p hp)) hJ_disj
            (fun _ _ ↦ (hX.integrable s).integrableOn)]
      _ ≤ μ[X t] - μ[X s] :=
        hX.setIntegral_sub_setIntegral_le hst (Finset.measurableSet_biUnion _ hJ_meas)
    calc ∑ p ∈ insert q I, (∫ ω in A p, X (min p.2 t) ω ∂μ - ∫ ω in A p, X (min p.1 t) ω ∂μ)
    _ = ∑ p ∈ insert q I, (∫ ω in A p, X (min p.2 (min s t)) ω ∂μ
          - ∫ ω in A p, X (min p.1 (min s t)) ω ∂μ)
        + ∑ p ∈ insert q I, (∫ ω in A p, X (min p.2 t) ω ∂μ
          - ∫ ω in A p, X (min p.2 (min s t)) ω ∂μ) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      rw [← min_assoc p.1, min_eq_left (hle_s p hp)]
      ring
    _ ≤ (μ[X (min s t)] - μ[X ⊥]) + (μ[X t] - μ[X (min s t)]) := add_le_add h_before h_after
    _ = μ[X t] - μ[X ⊥] := by ring

/-- The expectation of the elementary stochastic integral of the indicator of an elementary
predictable set against a submartingale `X` is bounded by `μ[X t] - μ[X ⊥]`. -/
lemma _root_.MeasureTheory.Submartingale.integral_elementaryPredictableSet_indicator_le
    [SigmaFiniteFiltration μ 𝓕] (hX : Submartingale X 𝓕 μ) (S : ElementaryPredictableSet 𝓕)
    (t : ι) :
    μ[(S.indicator (1 : ℝ) ● X) t] ≤ μ[X t] - μ[X ⊥] := by
  rw [ElementaryPredictableSet.integral_integral_indicator_one hX.integrable]
  simp_rw [integral_sub (hX.integrable _).integrableOn (hX.integrable _).integrableOn]
  exact hX.sum_setIntegral_sub_le_aux S.set S.I t S.le_of_mem_I S.measurableSet_set
    S.pairwiseDisjoint

lemma _root_.MeasureTheory.Submartingale.isRealQuasimartingale [SigmaFiniteFiltration μ 𝓕]
    (hX : Submartingale X 𝓕 μ) :
    IsRealQuasimartingale 𝓕 X μ :=
  ⟨hX.stronglyAdapted.adapted, hX.integrable,
    fun t ↦ ⟨μ[X t] - μ[X ⊥], fun S ↦ hX.integral_elementaryPredictableSet_indicator_le S t⟩⟩

end ProbabilityTheory
