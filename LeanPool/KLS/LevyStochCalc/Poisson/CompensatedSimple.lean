/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0, with
-- source adaptations (deprecated names, proof-context visibility) listed in vendor/port.patch.
module

public import LeanPool.KLS.LevyStochCalc.Poisson.RandomMeasure

/-!
# Compensated Poisson integral: simple predictable integrands

The simple predictable integrands `φ = ∑_i ξ_i · 1_{(t_i, t_{i+1}] × A_i}` and
their integral `simpleIntegral` against the compensated Poisson measure
`Ñ(dt, de) := N(dt, de) − ν(de) dt`, with the indicator/rectangle bookkeeping
lemmas. The moment identities are in `Poisson/CompensatedMoments.lean`; the
L²-isometry in `Poisson/CompensatedIsometry.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- A *simple predictable* integrand: a finite linear combination of
indicators on time-interval × measurable-set products. -/
structure SimplePredictable
    (Ω : Type u) [MeasurableSpace Ω]
    (E : Type v) [MeasurableSpace E]
    (ν : Measure E) [SigmaFinite ν]
    (T : ℝ) where
  /-- Number of partition pieces. -/
  N : ℕ
  /-- Time-partition points `0 = t_0 < t_1 < ⋯ < t_N ≤ T`. -/
  partition : Fin (N + 1) → ℝ
  partition_zero : partition 0 = 0
  partition_le_T : partition (Fin.last N) ≤ T
  partition_strictMono : StrictMono partition
  /-- Mark sets `A_i ⊆ E`, each measurable with `ν(A_i) < ∞`. -/
  A : Fin N → Set E
  A_measurable : ∀ i : Fin N, MeasurableSet (A i)
  A_finite : ∀ i : Fin N, ν (A i) ≠ ⊤
  /-- Per-piece bounded coefficients `ξ_i : Ω → ℝ`. -/
  ξ : Fin N → Ω → ℝ
  ξ_bounded : ∀ i : Fin N, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M
  ξ_measurable : ∀ i : Fin N, Measurable (ξ i)

open Classical in
/-- Evaluate a simple predictable integrand at fixed `(s, e)`. -/
noncomputable def SimplePredictable.eval
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (s : ℝ) (e : E) (ω : Ω) : ℝ :=
  ∑ i : Fin φ.N,
    if φ.partition i.castSucc < s ∧ s ≤ φ.partition i.succ ∧ e ∈ φ.A i
    then φ.ξ i ω else 0

/-- The time-rectangle `(t_i ∧ t, t_{i+1} ∧ t] × A_i` for the `i`-th piece
of the partition, evaluated at running time `t`. -/
noncomputable def SimplePredictable.timeRect
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) (t : ℝ) : Set (ℝ × E) :=
  Set.Ioc (min (φ.partition i.castSucc) t) (min (φ.partition i.succ) t) ×ˢ φ.A i

/-- The full time-rectangle `(t_i, t_{i+1}] × A_i` (independent of cutoff). -/
noncomputable def SimplePredictable.fullRect
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) : Set (ℝ × E) :=
  Set.Ioc (φ.partition i.castSucc) (φ.partition i.succ) ×ˢ φ.A i

/-- `eval` rewritten as a sum of indicator-valued terms over `fullRect i`. -/
lemma SimplePredictable.eval_eq_sum_indicator
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (s : ℝ) (e : E) (ω : Ω) :
    φ.eval s e ω = ∑ i : Fin φ.N,
      (φ.fullRect i).indicator (fun _ : ℝ × E => φ.ξ i ω) (s, e) := by
  unfold SimplePredictable.eval
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : φ.partition i.castSucc < s ∧ s ≤ φ.partition i.succ ∧ e ∈ φ.A i
  · rw [ite_eq_left h]
    have h_mem : (s, e) ∈ φ.fullRect i := by
      unfold SimplePredictable.fullRect
      exact Set.mem_prod.mpr ⟨Set.mem_Ioc.mpr ⟨h.1, h.2.1⟩, h.2.2⟩
    exact (Set.indicator_of_mem h_mem (fun _ : ℝ × E => φ.ξ i ω)).symm
  · rw [ite_eq_right h]
    have h_not_mem : (s, e) ∉ φ.fullRect i := by
      unfold SimplePredictable.fullRect
      intro hmem
      obtain ⟨ht, he⟩ := Set.mem_prod.mp hmem
      obtain ⟨h1, h2⟩ := Set.mem_Ioc.mp ht
      exact h ⟨h1, h2, he⟩
    exact (Set.indicator_of_notMem h_not_mem (fun _ : ℝ × E => φ.ξ i ω)).symm

/-- The full rectangles `(t_i, t_{i+1}] × A_i` for `i : Fin φ.N` are pairwise disjoint
(time intervals are disjoint). -/
lemma SimplePredictable.fullRect_disjoint
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) :
    Pairwise (fun i j : Fin φ.N => Disjoint (φ.fullRect i) (φ.fullRect j)) := by
  intro i j hij
  unfold SimplePredictable.fullRect
  rcases lt_or_gt_of_ne hij with h | h
  · have h_succ_le : φ.partition i.succ ≤ φ.partition j.castSucc :=
      φ.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr h)
    rw [Set.disjoint_iff]
    intro x hx
    obtain ⟨hxi, hxj⟩ := hx
    obtain ⟨hxi_t, _⟩ := Set.mem_prod.mp hxi
    obtain ⟨hxj_t, _⟩ := Set.mem_prod.mp hxj
    obtain ⟨_, hxi_le⟩ := Set.mem_Ioc.mp hxi_t
    obtain ⟨hxj_lt, _⟩ := Set.mem_Ioc.mp hxj_t
    exact absurd (hxi_le.trans h_succ_le) (not_le.mpr hxj_lt)
  · have h_succ_le : φ.partition j.succ ≤ φ.partition i.castSucc :=
      φ.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr h)
    rw [Set.disjoint_iff]
    intro x hx
    obtain ⟨hxi, hxj⟩ := hx
    obtain ⟨hxi_t, _⟩ := Set.mem_prod.mp hxi
    obtain ⟨hxj_t, _⟩ := Set.mem_prod.mp hxj
    obtain ⟨hxi_lt, _⟩ := Set.mem_Ioc.mp hxi_t
    obtain ⟨_, hxj_le⟩ := Set.mem_Ioc.mp hxj_t
    exact absurd (hxj_le.trans h_succ_le) (not_le.mpr hxi_lt)

/-- `referenceIntensity ν (fullRect i) = ENNReal.ofReal(t_{i+1} − t_i) · ν(A_i)`. -/
lemma SimplePredictable.referenceIntensity_fullRect
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) :
    LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i)
      = ENNReal.ofReal (φ.partition i.succ - φ.partition i.castSucc) * ν (φ.A i) := by
  unfold SimplePredictable.fullRect LevyStochCalc.Poisson.referenceIntensity
  rw [MeasureTheory.Measure.prod_prod]
  congr 1
  -- volume.restrict [0,∞) (Ioc t_i t_{i+1}) = volume (Ioc t_i t_{i+1})
  -- (since t_i ≥ 0, the interval is in [0,∞))
  have h_t_i_nn : 0 ≤ φ.partition i.castSucc := by
    have : φ.partition 0 ≤ φ.partition i.castSucc :=
      φ.partition_strictMono.monotone (Fin.zero_le _)
    rw [φ.partition_zero] at this
    exact this
  have h_subset :
      Set.Ioc (φ.partition i.castSucc) (φ.partition i.succ) ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    exact h_t_i_nn.trans (le_of_lt hx.1)
  rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioc]
  rw [Set.inter_eq_left.mpr h_subset]
  rw [Real.volume_Ioc]

/-- The double-lintegral of the constant-indicator on `fullRect i` over `[0, T] × E`
equals `c · referenceIntensity ν (fullRect i)`. -/
lemma SimplePredictable.lintegral_indicator_fullRect
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) (c : ℝ≥0∞) :
    ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (φ.fullRect i).indicator (fun _ : ℝ × E => c) (s, e) ∂ν ∂volume
      = c * LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i) := by
  have h_meas_fullRect : MeasurableSet (φ.fullRect i) := by
    unfold SimplePredictable.fullRect
    exact measurableSet_Ioc.prod (φ.A_measurable i)
  have h_t_i_nn : 0 ≤ φ.partition i.castSucc := by
    have : φ.partition 0 ≤ φ.partition i.castSucc :=
      φ.partition_strictMono.monotone (Fin.zero_le _)
    rw [φ.partition_zero] at this
    exact this
  have h_t_i_succ_le_T : φ.partition i.succ ≤ T :=
    le_trans (φ.partition_strictMono.monotone (Fin.le_last _)) φ.partition_le_T
  have h_subset_T :
      Set.Ioc (φ.partition i.castSucc) (φ.partition i.succ) ⊆ Set.Icc (0 : ℝ) T := by
    intro x hx
    exact ⟨h_t_i_nn.trans (le_of_lt hx.1), hx.2.trans h_t_i_succ_le_T⟩
  -- Convert iterated lintegral to product lintegral (Fubini).
  rw [MeasureTheory.lintegral_lintegral
    (f := fun s e => (φ.fullRect i).indicator (fun _ : ℝ × E => c) (s, e))
    (Measurable.indicator measurable_const h_meas_fullRect).aemeasurable]
  -- ∫⁻ z, ind (fullRect i) (fun _ => c) z ∂((volume.restrict [0,T]).prod ν)
  rw [show (fun (z : ℝ × E) => (φ.fullRect i).indicator (fun _ : ℝ × E => c) (z.1, z.2))
        = (φ.fullRect i).indicator (fun _ : ℝ × E => c) from by funext z; rfl]
  rw [MeasureTheory.lintegral_indicator_const h_meas_fullRect]
  -- c * ((volume.restrict (Icc 0 T)).prod ν)(fullRect i)
  -- = c * (volume.restrict (Icc 0 T))(Ioc) * ν(A_i)
  -- = c * volume(Ioc) * ν(A_i)
  -- = c * referenceIntensity ν (fullRect i)
  unfold SimplePredictable.fullRect LevyStochCalc.Poisson.referenceIntensity
  rw [MeasureTheory.Measure.prod_prod, MeasureTheory.Measure.prod_prod]
  rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioc]
  rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioc]
  rw [Set.inter_eq_left.mpr h_subset_T]
  have h_subset_Ici :
      Set.Ioc (φ.partition i.castSucc) (φ.partition i.succ) ⊆ Set.Ici (0 : ℝ) := by
    intro x hx; exact h_t_i_nn.trans (le_of_lt hx.1)
  rw [Set.inter_eq_left.mpr h_subset_Ici]

/-- `‖φ.eval s e ω‖₊²` decomposes as a sum of indicator-squares (disjoint rectangles). -/
lemma SimplePredictable.eval_sq_eq_sum_indicator
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (s : ℝ) (e : E) (ω : Ω) :
    (‖φ.eval s e ω‖₊ : ℝ≥0∞) ^ 2 = ∑ i : Fin φ.N,
      (φ.fullRect i).indicator (fun _ => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2) (s, e) := by
  rw [SimplePredictable.eval_eq_sum_indicator]
  by_cases h_any : ∃ i : Fin φ.N, (s, e) ∈ φ.fullRect i
  · obtain ⟨i₀, hi₀⟩ := h_any
    have h_unique : ∀ j : Fin φ.N, j ≠ i₀ → (s, e) ∉ φ.fullRect j := by
      intro j hj hj_mem
      have := φ.fullRect_disjoint hj
      exact Set.disjoint_left.mp this hj_mem hi₀
    have h_sum_eq : (∑ i : Fin φ.N,
        (φ.fullRect i).indicator (fun _ => φ.ξ i ω) (s, e)) = φ.ξ i₀ ω := by
      rw [Finset.sum_eq_single i₀]
      · exact Set.indicator_of_mem hi₀ _
      · intro j _ hj
        exact Set.indicator_of_notMem (h_unique j hj) _
      · intro h_not; exact absurd (Finset.mem_univ _) h_not
    have h_sum_sq_eq : (∑ i : Fin φ.N,
        (φ.fullRect i).indicator (fun _ => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2) (s, e))
        = (‖φ.ξ i₀ ω‖₊ : ℝ≥0∞) ^ 2 := by
      rw [Finset.sum_eq_single i₀]
      · exact Set.indicator_of_mem hi₀ _
      · intro j _ hj
        exact Set.indicator_of_notMem (h_unique j hj) _
      · intro h_not; exact absurd (Finset.mem_univ _) h_not
    rw [h_sum_eq, h_sum_sq_eq]
  · push Not at h_any
    have h_zero : ∀ i : Fin φ.N, (φ.fullRect i).indicator (fun _ => φ.ξ i ω) (s, e) = 0 :=
      fun i => Set.indicator_of_notMem (h_any i) _
    have h_zero_sq : ∀ i : Fin φ.N,
        (φ.fullRect i).indicator (fun _ => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2) (s, e) = 0 :=
      fun i => Set.indicator_of_notMem (h_any i) _
    rw [Finset.sum_eq_zero (fun i _ => h_zero i),
        Finset.sum_eq_zero (fun i _ => h_zero_sq i)]
    simp

/-- The inner double-lintegral of `‖φ.eval‖²` over `[0, T] × E`. -/
lemma SimplePredictable.lintegral_eval_sq
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (ω : Ω) :
    ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume
      = ∑ i : Fin φ.N,
        (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2
          * LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i) := by
  -- Pointwise: replace eval² with sum of indicators.
  simp_rw [SimplePredictable.eval_sq_eq_sum_indicator φ _ _ ω]
  -- Pull inner sum out via lintegral_finset_sum.
  have h_inner_meas : ∀ s : ℝ, ∀ i : Fin φ.N,
      Measurable (fun e : E =>
        (φ.fullRect i).indicator
          (fun _ : ℝ × E => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2) (s, e)) := by
    intro s i
    have h_meas_fullRect : MeasurableSet (φ.fullRect i) := by
      unfold SimplePredictable.fullRect
      exact measurableSet_Ioc.prod (φ.A_measurable i)
    have h_meas_ind : Measurable
        ((φ.fullRect i).indicator (fun _ : ℝ × E => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2)) :=
      Measurable.indicator measurable_const h_meas_fullRect
    exact h_meas_ind.comp measurable_prodMk_left
  rw [show (fun s : ℝ => ∫⁻ e, ∑ i : Fin φ.N,
        (φ.fullRect i).indicator
          (fun _ : ℝ × E => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2) (s, e) ∂ν)
        = (fun s : ℝ => ∑ i : Fin φ.N, ∫⁻ e,
            (φ.fullRect i).indicator
              (fun _ : ℝ × E => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2) (s, e) ∂ν) from by
    funext s
    exact MeasureTheory.lintegral_finsetSum _ (fun i _ => h_inner_meas s i)]
  -- Pull outer sum out.
  have h_outer_meas : ∀ i : Fin φ.N,
      Measurable (fun s : ℝ => ∫⁻ e,
        (φ.fullRect i).indicator
          (fun _ : ℝ × E => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2) (s, e) ∂ν) := by
    intro i
    have h_meas_fullRect : MeasurableSet (φ.fullRect i) := by
      unfold SimplePredictable.fullRect
      exact measurableSet_Ioc.prod (φ.A_measurable i)
    have h_meas_ind : Measurable
        ((φ.fullRect i).indicator (fun _ : ℝ × E => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2)) :=
      Measurable.indicator measurable_const h_meas_fullRect
    exact h_meas_ind.lintegral_prod_right'
  rw [MeasureTheory.lintegral_finsetSum _ (fun i _ => h_outer_meas i)]
  -- Apply per-term identity.
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [SimplePredictable.lintegral_indicator_fullRect φ i]

/-- The outer triple-lintegral (`∂P` outermost) of `‖φ.eval‖²`. Reduces to
`∑_i ν̂(fullRect i) · ∫⁻ ω, ‖ξ_i ω‖² ∂P` — the canonical RHS form of the
Itô-Lévy isometry. -/
lemma SimplePredictable.lintegral_eval_sq_outer
    {P : Measure Ω}
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P
      = ∑ i : Fin φ.N,
        LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i) *
        ∫⁻ ω, (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  -- Step 1: rewrite inner double-lintegral via lintegral_eval_sq.
  rw [show (fun ω : Ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
              (‖φ.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume)
        = (fun ω : Ω => ∑ i : Fin φ.N,
            (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2 *
            LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i)) from
    funext (fun ω => SimplePredictable.lintegral_eval_sq φ ω)]
  -- Step 2: pull outer sum out via lintegral_finset_sum.
  have h_sq_meas : ∀ i : Fin φ.N,
      Measurable (fun ω : Ω => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2) := by
    intro i
    refine Measurable.pow_const ?_ 2
    exact ENNReal.continuous_coe.measurable.comp (φ.ξ_measurable i).nnNorm
  rw [MeasureTheory.lintegral_finsetSum]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [MeasureTheory.lintegral_mul_const _ (h_sq_meas i)]
    ring
  · intro i _
    exact (h_sq_meas i).mul_const _

/-- Integral of a simple predictable integrand against the compensated
Poisson random measure:

  `∑_i ξ_i · [N((t_i ∧ t, t_{i+1} ∧ t] × A_i)`
  `      − ((t_{i+1} ∧ t − t_i ∧ t)·ν(A_i))]`

Using the `compensated` field of the time-aware `PoissonRandomMeasure`. -/
noncomputable def simpleIntegral
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin φ.N,
    φ.ξ i ω * N.compensated (φ.timeRect i t) ω

/-- The simple integral at time `0` is identically zero: each time-rectangle
`(t_i ∧ 0, t_{i+1} ∧ 0]` is empty (since `partition_zero` and `partition_strictMono`
give `0 ≤ partition i.castSucc`, hence `min · 0 = 0`), and the compensated
measure of the empty set is `0`. -/
lemma simpleIntegral_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (ω : Ω) :
    simpleIntegral N φ 0 ω = 0 := by
  unfold simpleIntegral
  apply Finset.sum_eq_zero
  intro i _
  -- Show: φ.timeRect i 0 = ∅, hence compensated value = 0.
  have h_zero_le_castSucc : φ.partition 0 ≤ φ.partition i.castSucc :=
    φ.partition_strictMono.monotone (Fin.zero_le i.castSucc)
  have h_zero_le_succ : φ.partition 0 ≤ φ.partition i.succ :=
    φ.partition_strictMono.monotone (Fin.zero_le i.succ)
  rw [φ.partition_zero] at h_zero_le_castSucc h_zero_le_succ
  have h_min_castSucc : min (φ.partition i.castSucc) 0 = 0 :=
    min_eq_right h_zero_le_castSucc
  have h_min_succ : min (φ.partition i.succ) 0 = 0 := min_eq_right h_zero_le_succ
  have h_rect_empty : φ.timeRect i 0 = ∅ := by
    unfold SimplePredictable.timeRect
    rw [h_min_castSucc, h_min_succ]
    rw [Set.Ioc_self]
    exact Set.empty_prod
  rw [h_rect_empty]
  -- compensated of ∅ is 0
  unfold LevyStochCalc.Poisson.PoissonRandomMeasure.compensated
  simp
end LevyStochCalc.Poisson.Compensated
