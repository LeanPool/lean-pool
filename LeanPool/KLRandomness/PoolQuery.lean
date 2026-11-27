/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.DropEvents
public import LeanPool.KLRandomness.ComputableNonrandom
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith

/-!
# Query indicators on answer space

The pool lemma feeds the same answer sequence to several scan rules. Its
probability space is therefore answer space, rather than the original input
space of an adaptive run. The query at time `t` is the rule applied directly
to the first `t` prescribed answers.

Every finite pool's coverage fraction stabilizes pointwise at a finite
horizon (depending on the answer sequence). The actual finite-horizon
fractions converge in L¹, as required by the pool search's termination proof.
-/

@[expose] public section

namespace Klr.PoolQuery

open MeasureTheory Filter
open scoped Topology BigOperators

/-- The query made after the first `t` bits of a prescribed answer sequence. -/
def queryAt (π : ScanRule) (Z : Cantor) (t : ℕ) : ℕ :=
  π.query (ScanRule.inputPrefix Z t)

/-- A position is queried before a finite horizon. -/
def ReadsBy (π : ScanRule) (a V : ℕ) (Z : Cantor) : Prop :=
  ∃ t < V, queryAt π Z t = a

/-- A position is queried at some time on the prescribed answer sequence. -/
def Reads (π : ScanRule) (a : ℕ) (Z : Cantor) : Prop :=
  ∃ t, queryAt π Z t = a

theorem measurable_queryAt (π : ScanRule) (t : ℕ) :
    Measurable (fun Z => queryAt π Z t) := by
  simpa only [ScanRule.monotone_transcript, queryAt] using
    DropEvents.measurable_transcript_eval ScanRule.monotone t π.query

theorem measurableSet_readsBy (π : ScanRule) (a V : ℕ) :
    MeasurableSet {Z | ReadsBy π a V Z} := by
  have he : {Z | ReadsBy π a V Z} =
      ⋃ t : Fin V, {Z | queryAt π Z t.val = a} := by
    ext Z
    simp only [ReadsBy, Set.mem_ofPred_eq, Set.mem_iUnion]
    exact ⟨fun ⟨t, ht, h⟩ => ⟨⟨t, ht⟩, h⟩,
      fun ⟨t, h⟩ => ⟨t.val, t.isLt, h⟩⟩
  rw [he]
  exact MeasurableSet.iUnion fun t => (measurable_queryAt π t.val) (measurableSet_singleton a)

theorem measurableSet_reads (π : ScanRule) (a : ℕ) :
    MeasurableSet {Z | Reads π a Z} := by
  have he : {Z | Reads π a Z} = ⋃ t : ℕ, {Z | queryAt π Z t = a} := by
    ext Z
    simp [Reads]
  rw [he]
  exact MeasurableSet.iUnion fun t => (measurable_queryAt π t) (measurableSet_singleton a)

theorem readsBy_mono (π : ScanRule) (a : ℕ) {V W : ℕ} (hVW : V ≤ W) {Z : Cantor}
    (h : ReadsBy π a V Z) : ReadsBy π a W Z := by
  obtain ⟨t, ht, hq⟩ := h
  exact ⟨t, lt_of_lt_of_le ht hVW, hq⟩

theorem reads_of_readsBy {π : ScanRule} {a V : ℕ} {Z : Cantor}
    (h : ReadsBy π a V Z) : Reads π a Z := by
  obtain ⟨t, _, ht⟩ := h
  exact ⟨t, ht⟩

/-- The indicator of eventual querying, denoted `g_{i,a}` in the paper. -/
noncomputable def indicator (π : ScanRule) (a : ℕ) : Cantor → ℝ :=
  {Z | Reads π a Z}.indicator (fun _ => 1)

/-- The finite-horizon query indicator. -/
noncomputable def indicatorBy (π : ScanRule) (a V : ℕ) : Cantor → ℝ :=
  {Z | ReadsBy π a V Z}.indicator (fun _ => 1)

theorem measurable_indicator (π : ScanRule) (a : ℕ) : Measurable (indicator π a) :=
  measurable_const.indicator (measurableSet_reads π a)

theorem measurable_indicatorBy (π : ScanRule) (a V : ℕ) : Measurable (indicatorBy π a V) :=
  measurable_const.indicator (measurableSet_readsBy π a V)

theorem indicator_bounds (π : ScanRule) (a : ℕ) (Z : Cantor) :
    0 ≤ indicator π a Z ∧ indicator π a Z ≤ 1 := by
  classical
  by_cases h : Reads π a Z <;> simp [indicator, h]

theorem indicatorBy_bounds (π : ScanRule) (a V : ℕ) (Z : Cantor) :
    0 ≤ indicatorBy π a V Z ∧ indicatorBy π a V Z ≤ 1 := by
  classical
  by_cases h : ReadsBy π a V Z <;> simp [indicatorBy, h]

theorem integrable_indicator (π : ScanRule) (a : ℕ) : Integrable (indicator π a) fairCoin :=
  (integrable_const (1 : ℝ)).indicator (measurableSet_reads π a)

theorem integrable_indicatorBy (π : ScanRule) (a V : ℕ) :
    Integrable (indicatorBy π a V) fairCoin :=
  (integrable_const (1 : ℝ)).indicator (measurableSet_readsBy π a V)

theorem indicatorBy_le_indicator (π : ScanRule) (a V : ℕ) (Z : Cantor) :
    indicatorBy π a V Z ≤ indicator π a Z := by
  classical
  by_cases h : ReadsBy π a V Z
  · simp [indicatorBy, indicator, h, reads_of_readsBy h]
  · simpa [indicatorBy, h] using (indicator_bounds π a Z).1

/-- For one position, the finite query indicator eventually equals its limit
on every prescribed answer sequence. -/
theorem eventually_indicatorBy_eq (π : ScanRule) (a : ℕ) (Z : Cantor) :
    ∀ᶠ V : ℕ in atTop, indicatorBy π a V Z = indicator π a Z := by
  classical
  by_cases h : Reads π a Z
  · obtain ⟨t, ht⟩ := h
    filter_upwards [eventually_ge_atTop (t + 1)] with V hV
    have hb : ReadsBy π a V Z := ⟨t, by omega, ht⟩
    simp [indicatorBy, indicator, hb, reads_of_readsBy hb]
  · filter_upwards [] with V
    have hb : ¬ ReadsBy π a V Z := fun hb => h (reads_of_readsBy hb)
    simp [indicatorBy, indicator, hb, h]

/-- Fraction of the finite pool queried eventually. -/
noncomputable def readFraction (π : ScanRule) (G : Finset ℕ) (Z : Cantor) : ℝ :=
  (∑ a ∈ G, indicator π a Z) / G.card

/-- Fraction of the finite pool queried before the stated horizon. -/
noncomputable def readFractionBy (π : ScanRule) (G : Finset ℕ) (V : ℕ) (Z : Cantor) : ℝ :=
  (∑ a ∈ G, indicatorBy π a V Z) / G.card

theorem measurable_readFraction (π : ScanRule) (G : Finset ℕ) :
    Measurable (readFraction π G) := by
  exact (Finset.measurable_sum G fun a _ => measurable_indicator π a).div_const _

theorem measurable_readFractionBy (π : ScanRule) (G : Finset ℕ) (V : ℕ) :
    Measurable (readFractionBy π G V) := by
  exact (Finset.measurable_sum G fun a _ => measurable_indicatorBy π a V).div_const _

theorem readFraction_nonneg (π : ScanRule) (G : Finset ℕ) (Z : Cantor) :
    0 ≤ readFraction π G Z :=
  div_nonneg (Finset.sum_nonneg fun a _ => (indicator_bounds π a Z).1) (Nat.cast_nonneg _)

theorem readFractionBy_nonneg (π : ScanRule) (G : Finset ℕ) (V : ℕ) (Z : Cantor) :
    0 ≤ readFractionBy π G V Z :=
  div_nonneg (Finset.sum_nonneg fun a _ => (indicatorBy_bounds π a V Z).1) (Nat.cast_nonneg _)

theorem readFraction_le_one (π : ScanRule) (G : Finset ℕ) (Z : Cantor) :
    readFraction π G Z ≤ 1 := by
  by_cases hG : G.card = 0
  · simp [readFraction, hG]
  · apply (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hG)).mpr
    calc
      (∑ a ∈ G, indicator π a Z) ≤ ∑ _a ∈ G, (1 : ℝ) :=
        Finset.sum_le_sum fun a _ => (indicator_bounds π a Z).2
      _ = _ := by simp

theorem readFractionBy_le_readFraction (π : ScanRule) (G : Finset ℕ) (V : ℕ) (Z : Cantor) :
    readFractionBy π G V Z ≤ readFraction π G Z :=
  div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun a _ => indicatorBy_le_indicator π a V Z) (Nat.cast_nonneg _)

theorem integrable_readFraction (π : ScanRule) (G : Finset ℕ) :
    Integrable (readFraction π G) fairCoin :=
  (integrable_finsetSum G fun a _ => integrable_indicator π a).div_const _

theorem integrable_readFractionBy (π : ScanRule) (G : Finset ℕ) (V : ℕ) :
    Integrable (readFractionBy π G V) fairCoin :=
  (integrable_finsetSum G fun a _ => integrable_indicatorBy π a V).div_const _

/-- Every finite pool has a path-dependent horizon capturing all positions
that will ever be queried on that path. -/
theorem eventually_readFractionBy_eq (π : ScanRule) (G : Finset ℕ) (Z : Cantor) :
    ∀ᶠ V : ℕ in atTop, readFractionBy π G V Z = readFraction π G Z := by
  have h := (eventually_all_finset G).mpr (fun a _ => eventually_indicatorBy_eq π a Z)
  filter_upwards [h] with V hV
  exact congrArg (fun s : ℝ => s / G.card) (Finset.sum_congr rfl hV)

/-- The finite-horizon coverage fractions converge in the actual L¹ norm. -/
theorem tendsto_readFractionBy_l1 (π : ScanRule) (G : Finset ℕ) :
    Tendsto (fun V : ℕ => ∫ Z, |readFraction π G Z - readFractionBy π G V Z| ∂fairCoin)
      atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := fairCoin)
    (F := fun V Z => |readFraction π G Z - readFractionBy π G V Z|)
    (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
    (fun V => by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using ((measurable_readFraction π G).sub
        (measurable_readFractionBy π G V)).norm.aestronglyMeasurable)
    (integrable_const 1) (fun V => Filter.Eventually.of_forall fun Z => by
      rw [Real.norm_eq_abs, abs_abs, abs_of_nonneg
        (sub_nonneg.mpr (readFractionBy_le_readFraction π G V Z))]
      linarith [readFraction_le_one π G Z, readFractionBy_nonneg π G V Z])
    (Filter.Eventually.of_forall fun Z => by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_readFractionBy_eq π G Z] with V hV
      simp [hV])
  simpa using h

end Klr.PoolQuery
