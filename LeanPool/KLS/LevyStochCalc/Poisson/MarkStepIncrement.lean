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

public import LeanPool.KLS.LevyStochCalc.Poisson.MarkStepWeight

/-!
# Dyadic mark-step integrands and their weighted increments

On the dyadic grids `TimeGrid.dyadic T hT n` of `[0, T]`, a mark-step integrand of level
`n` is re-expressed on any finer level `m ≥ n` (`MarkStep.dyadicRefine`), each fine piece
inheriting the coefficients of the coarse piece containing it, and is restricted to a
horizon `T'` with `T = T' * 2 ^ d` (`MarkStep.dyadicRestrict`); both leave the compensated
integral and the integrand unchanged. The increment of a mark-step integrand over `(s, t]`,
weighted by a bounded measurable `w`, is itself a mark-step integrand on the increment grid
`TimeGrid.incr` (`MarkStep.incr`), which gives the `L²` isometry for such increments.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

namespace MarkStep

section Dyadic

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The dyadic grid of level `n` on `[0, T]`. -/
noncomputable def _root_.LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic (T : ℝ) (hT : 0 < T)
    (n : ℕ) : TimeGrid where
  N₀ := 2 ^ n
  p := fun i => (i : ℝ) * T / (2 ^ n : ℕ)
  p_zero := by simp
  p_lt := fun i _ => by
    have h : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
    rw [div_lt_div_iff_of_pos_right h]
    push_cast
    nlinarith

lemma _root_.LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic_horizon (T : ℝ) (hT : 0 < T)
    (n : ℕ) : (TimeGrid.dyadic T hT n).horizon = T := by
  change ((2 ^ n : ℕ) : ℝ) * T / (2 ^ n : ℕ) = T
  field_simp

lemma _root_.LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic_p_castSucc (T : ℝ) (hT : 0 < T)
    (n : ℕ) (i : Fin (2 ^ n)) :
    (TimeGrid.dyadic T hT n).p i = dyadicPartition T n i.castSucc := rfl

lemma _root_.LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic_p_succ (T : ℝ) (hT : 0 < T)
    (n : ℕ) (i : Fin (2 ^ n)) :
    (TimeGrid.dyadic T hT n).p (i + 1) = dyadicPartition T n i.succ := rfl

variable {T : ℝ} {hT : 0 < T} {n m : ℕ}

/-- A mark-step integrand on the level-`n` dyadic grid, re-expressed on the level-`m`
dyadic grid (`n ≤ m`): each fine piece inherits the coefficients of the coarse piece
containing it. -/
def dyadicRefine (G : MarkStep Ω E ν (TimeGrid.dyadic T hT n)) (_hnm : n ≤ m) :
    MarkStep Ω E ν (TimeGrid.dyadic T hT m) where
  K := G.K
  B := G.B
  B_measurable := G.B_measurable
  B_finite := G.B_finite
  ξ := fun i k => G.ξ (i / 2 ^ (m - n)) k
  ξ_bounded := fun _ k => G.ξ_bounded _ k
  ξ_measurable := fun _ k => G.ξ_measurable _ k

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G : MarkStep Ω E ν (TimeGrid.dyadic T hT n))
  (hnm : n ≤ m)

lemma full_dyadicRefine : (fun ω => (G.dyadicRefine hnm).full N ω) =ᵐ[P] fun ω => G.full N ω := by
  have h := stepIntegral_dyadic_refine_integral N hT hnm (Ki := fun _ => G.K) (fun _ => G.B)
    (fun i k => G.ξ i k) (fun _ k => G.B_measurable k) (fun _ k => G.B_finite k)
  filter_upwards [h] with ω hω
  rw [full_eq_fin, full_eq_fin]
  exact hω

lemma eval_dyadicRefine (s : ℝ) (e : E) (ω : Ω) :
    (G.dyadicRefine hnm).eval s e ω = G.eval s e ω := by
  rw [eval_eq_fin, eval_eq_fin]
  exact stepIntegral_dyadic_refine_eval hT hnm (Ki := fun _ => G.K) (fun _ => G.B)
    (fun i k => G.ξ i k) s ω e

lemma Adapted.dyadicRefine (N : PoissonRandomMeasure P ν)
    {G : MarkStep Ω E ν (TimeGrid.dyadic T hT n)} (hG : G.Adapted ℱ) (hnm : n ≤ m) :
    (G.dyadicRefine hnm).Adapted ℱ := by
  intro i hi k
  exact dyadic_refine_adapted N ℱ hT hnm (Ki := fun _ => G.K) (fun i k => G.ξ i k)
    (fun i k => hG i i.isLt k) ⟨i, hi⟩ k

include hℱ in
/-- The integral of a refined adapted mark-step integrand agrees almost surely with the
integral of the integrand at every time. -/
lemma integral_dyadicRefine (hG : G.Adapted ℱ) (t : ℝ) :
    (fun ω => (G.dyadicRefine hnm).integral N t ω) =ᵐ[P] fun ω => G.integral N t ω := by
  have hfull : (fun ω => (G.dyadicRefine hnm).integral N T ω)
      =ᵐ[P] fun ω => G.integral N T ω := by
    have h1 : ∀ ω, (G.dyadicRefine hnm).integral N T ω = (G.dyadicRefine hnm).full N ω :=
      fun ω => (G.dyadicRefine hnm).integral_eq_full_of_horizon_le N
        (TimeGrid.dyadic_horizon T hT m).le ω
    have h2 : ∀ ω, G.integral N T ω = G.full N ω :=
      fun ω => G.integral_eq_full_of_horizon_le N (TimeGrid.dyadic_horizon T hT n).le ω
    simp only [h1, h2]
    exact G.full_dyadicRefine N hnm
  rcases le_or_gt t T with htT | htT
  · have hM₁ := (G.dyadicRefine hnm).martingale_integral N hℱ (hG.dyadicRefine N hnm)
    have hM₂ := G.martingale_integral N hℱ hG
    exact (hM₁.condExp_ae_eq htT).symm.trans
      ((condExp_congr_ae hfull).trans (hM₂.condExp_ae_eq htT))
  · have h1 : ∀ ω, (G.dyadicRefine hnm).integral N t ω = (G.dyadicRefine hnm).full N ω :=
      fun ω => (G.dyadicRefine hnm).integral_eq_full_of_horizon_le N
        ((TimeGrid.dyadic_horizon T hT m).le.trans htT.le) ω
    have h2 : ∀ ω, G.integral N t ω = G.full N ω :=
      fun ω => G.integral_eq_full_of_horizon_le N
        ((TimeGrid.dyadic_horizon T hT n).le.trans htT.le) ω
    simp only [h1, h2]
    exact G.full_dyadicRefine N hnm

/-- A mark-step integrand on the level-`ℓ` dyadic grid of `[0, T]`, restricted to the
prefix `[0, T']` where `T = T' * 2 ^ d` (`d ≤ ℓ`), which is the level-`(ℓ - d)` dyadic
grid there. -/
def dyadicRestrict {ℓ d : ℕ} (G : MarkStep Ω E ν (TimeGrid.dyadic T hT ℓ)) {T' : ℝ}
    (hT' : 0 < T') (_hd : d ≤ ℓ) (_h : T = T' * 2 ^ d) :
    MarkStep Ω E ν (TimeGrid.dyadic T' hT' (ℓ - d)) where
  K := G.K
  B := G.B
  B_measurable := G.B_measurable
  B_finite := G.B_finite
  ξ := G.ξ
  ξ_bounded := G.ξ_bounded
  ξ_measurable := G.ξ_measurable

lemma dyadic_p_restrict {ℓ d : ℕ} {T' : ℝ} (hT' : 0 < T') (hd : d ≤ ℓ) (h : T = T' * 2 ^ d)
    (i : ℕ) : (TimeGrid.dyadic T' hT' (ℓ - d)).p i = (TimeGrid.dyadic T hT ℓ).p i := by
  change (i : ℝ) * T' / ((2 ^ (ℓ - d) : ℕ) : ℝ) = (i : ℝ) * T / ((2 ^ ℓ : ℕ) : ℝ)
  have h2 : (2 : ℝ) ^ ℓ = 2 ^ d * 2 ^ (ℓ - d) := by rw [← pow_add, Nat.add_sub_cancel' hd]
  push_cast
  rw [h2, h]
  field_simp

lemma dyadic_p_pow {ℓ d : ℕ} {T' : ℝ} (hd : d ≤ ℓ) (h : T = T' * 2 ^ d) :
    (TimeGrid.dyadic T hT ℓ).p (2 ^ (ℓ - d)) = T' := by
  change ((2 ^ (ℓ - d) : ℕ) : ℝ) * T / ((2 ^ ℓ : ℕ) : ℝ) = T'
  have h2 : (2 : ℝ) ^ ℓ = 2 ^ d * 2 ^ (ℓ - d) := by rw [← pow_add, Nat.add_sub_cancel' hd]
  push_cast
  rw [h2, h]
  field_simp

lemma full_dyadicRestrict {ℓ d : ℕ} (G : MarkStep Ω E ν (TimeGrid.dyadic T hT ℓ)) {T' : ℝ}
    (hT' : 0 < T') (hd : d ≤ ℓ) (h : T = T' * 2 ^ d) (ω : Ω) :
    (G.dyadicRestrict hT' hd h).full N ω = G.integral N T' ω := by
  have h' : (G.dyadicRestrict hT' hd h).full N ω
      = G.integral N ((TimeGrid.dyadic T hT ℓ).p (2 ^ (ℓ - d))) ω := by
    rw [G.integral_p_eq N _ (Nat.pow_le_pow_right two_pos (Nat.sub_le ℓ d))]
    unfold full
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    change G.ξ i k ω * N.compensated (Set.Ioc
        ((TimeGrid.dyadic T' hT' (ℓ - d)).p i)
        ((TimeGrid.dyadic T' hT' (ℓ - d)).p (i + 1)) ×ˢ G.B k) ω = _
    rw [dyadic_p_restrict (hT := hT) hT' hd h, dyadic_p_restrict (hT := hT) hT' hd h]
  rw [h', dyadic_p_pow (hT := hT) hd h]

lemma eval_dyadicRestrict {ℓ d : ℕ} (G : MarkStep Ω E ν (TimeGrid.dyadic T hT ℓ)) {T' : ℝ}
    (hT' : 0 < T') (hd : d ≤ ℓ) (h : T = T' * 2 ^ d) {s : ℝ} (hs : s ≤ T') (e : E) (ω : Ω) :
    (G.dyadicRestrict hT' hd h).eval s e ω = G.eval s e ω := by
  unfold eval
  simp_rw [dyadic_p_restrict (hT := hT) hT' hd h]
  refine Finset.sum_subset (Finset.range_subset.2 fun i hi =>
    Finset.mem_range.2 (lt_of_lt_of_le hi (Nat.pow_le_pow_right two_pos (Nat.sub_le ℓ d)))) ?_
  intro i hi hni
  rw [Finset.mem_range] at hi hni
  rw [Set.indicator_of_notMem, zero_mul]
  intro hs'
  have : (TimeGrid.dyadic T hT ℓ).p (2 ^ (ℓ - d)) ≤ (TimeGrid.dyadic T hT ℓ).p i :=
    (TimeGrid.dyadic T hT ℓ).p_mono (not_lt.1 hni) hi.le
  rw [dyadic_p_pow (hT := hT) hd h] at this
  exact absurd (hs.trans this) (not_le.2 hs'.1)

lemma Adapted.dyadicRestrict {ℓ d : ℕ}
    {G : MarkStep Ω E ν (TimeGrid.dyadic T hT ℓ)} (hG : G.Adapted ℱ) {T' : ℝ} (hT' : 0 < T')
    (hd : d ≤ ℓ) (h : T = T' * 2 ^ d) : (G.dyadicRestrict hT' hd h).Adapted ℱ := by
  intro i hi k
  change @StronglyMeasurable Ω ℝ _ (ℱ ((TimeGrid.dyadic T' hT' (ℓ - d)).p i)) (G.ξ i k)
  rw [dyadic_p_restrict (hT := hT) hT' hd h]
  exact hG i (lt_of_lt_of_le hi (Nat.pow_le_pow_right two_pos (Nat.sub_le ℓ d))) k

end Dyadic

section Increment

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

/-- The increment of a mark-step integrand over `(s, t]`, weighted by `w`, as a mark-step
integrand on the increment grid. -/
noncomputable def incr (G : MarkStep Ω E ν g) (w : Ω → ℝ) (hw : ∃ C : ℝ, ∀ ω, |w ω| ≤ C)
    (hwm : Measurable w) (s t : ℝ) (hs : 0 < s) (hst : s < t) :
    MarkStep Ω E ν (g.incr s t hs hst) where
  K := G.K
  B := G.B
  B_measurable := G.B_measurable
  B_finite := G.B_finite
  ξ := fun i k ω => if i = 0 then 0 else w ω * G.ξ (g.startIndex s + (i - 1)) k ω
  ξ_bounded := fun i k => by
    obtain ⟨C, hC⟩ := hw
    obtain ⟨M, hM⟩ := G.ξ_bounded (g.startIndex s + (i - 1)) k
    refine ⟨|C| * |M|, fun ω => ?_⟩
    split_ifs
    · rw [abs_zero]
      positivity
    · rw [abs_mul]
      exact mul_le_mul ((hC ω).trans (le_abs_self C)) ((hM ω).trans (le_abs_self M))
        (abs_nonneg _) (abs_nonneg _)
  ξ_measurable := fun i k => by
    by_cases h : i = 0
    · simp only [h, ite_true]
      exact measurable_const
    · simp only [h, ite_false]
      exact hwm.mul (G.ξ_measurable _ k)

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G : MarkStep Ω E ν g) {w : Ω → ℝ}
  (hw : ∃ C : ℝ, ∀ ω, |w ω| ≤ C) (hwm : Measurable w) {s t : ℝ} (hs : 0 < s) (hst : s < t)

include hw hwm in
lemma Adapted.incr {G : MarkStep Ω E ν g} (hG : G.Adapted ℱ)
    (hwa : @StronglyMeasurable Ω ℝ _ (ℱ s) w) :
    (G.incr w hw hwm s t hs hst).Adapted ℱ := by
  intro i hi k
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    change @StronglyMeasurable Ω ℝ _ (ℱ ((g.incr s t hs hst).p 0))
      (fun ω => if (0 : ℕ) = 0 then (0 : ℝ) else w ω * G.ξ (g.startIndex s + (0 - 1)) k ω)
    simp only [ite_true]
    exact stronglyMeasurable_const
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hi' : j + 1 < g.clampIndex t - g.startIndex s + 1 := hi
    have hj : g.startIndex s + j < g.clampIndex t := by omega
    have hlt := g.lt_of_lt_clampIndex hj
    change @StronglyMeasurable Ω ℝ _ (ℱ ((g.incr s t hs hst).p (j + 1)))
      (fun ω => if j + 1 = 0 then (0 : ℝ) else w ω * G.ξ (g.startIndex s + (j + 1 - 1)) k ω)
    simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
    rw [g.incr_p_succ]
    have hξ := hG (g.startIndex s + j) hlt.1 k
    rcases Nat.eq_zero_or_pos j with hz | hz
    · subst hz
      rw [add_zero, max_eq_right (g.p_startIndex_le hs.le), min_eq_left hst.le]
      rw [add_zero] at hξ
      exact hwa.mul (hξ.mono (ℱ.mono (g.p_startIndex_le hs.le)))
    · have haN : g.startIndex s < g.N₀ := lt_of_le_of_lt (Nat.le_add_right _ _) hlt.1
      have hgt : s < g.p (g.startIndex s + j) :=
        (g.lt_p_succ_startIndex haN).trans_le (g.p_mono (by omega) hlt.1.le)
      rw [max_eq_left hgt.le, min_eq_left hlt.2.le]
      exact (hwa.mono (ℱ.mono hgt.le)).mul hξ

/-- The integrand of the weighted increment, as a sum over the pieces meeting `(s, t]`. -/
lemma eval_incr_eq (σ : ℝ) (e : E) (ω : Ω) :
    (G.incr w hw hwm s t hs hst).eval σ e ω
      = ∑ j ∈ Finset.range (g.clampIndex t - g.startIndex s),
        (Set.Ioc (min (max (g.p (g.startIndex s + j)) s) t)
          (min (max (g.p (g.startIndex s + (j + 1))) s) t)).indicator (fun _ => (1 : ℝ)) σ
        * ∑ k, (w ω * G.ξ (g.startIndex s + j) k ω) * (G.B k).indicator (fun _ => (1 : ℝ)) e := by
  unfold eval
  change ∑ i ∈ Finset.range (g.clampIndex t - g.startIndex s + 1),
      (Set.Ioc ((g.incr s t hs hst).p i) ((g.incr s t hs hst).p (i + 1))).indicator
        (fun _ => (1 : ℝ)) σ
      * ∑ k, (if i = 0 then (0 : ℝ) else w ω * G.ξ (g.startIndex s + (i - 1)) k ω)
        * (G.B k).indicator (fun _ => (1 : ℝ)) e = _
  rw [Finset.sum_range_succ']
  simp only [ite_true, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [g.incr_p_succ, g.incr_p_succ]
  simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]

/-- The integrand of the weighted increment. -/
lemma eval_incr (σ : ℝ) (e : E) (ω : Ω) :
    (G.incr w hw hwm s t hs hst).eval σ e ω
      = if s < σ ∧ σ ≤ t then w ω * G.eval σ e ω else 0 := by
  rw [eval_incr_eq]
  have hab : g.startIndex s ≤ g.clampIndex t := g.startIndex_le_clampIndex hs.le hst
  have hbN : g.clampIndex t ≤ g.N₀ := g.clampIndex_le t
  split_ifs with hσ
  · -- restrict `G.eval` to the pieces `a ≤ i < b`
    have hG : G.eval σ e ω = ∑ i ∈ Finset.Ico (g.startIndex s) (g.clampIndex t),
        (Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) σ
          * ∑ k, G.ξ i k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e := by
      unfold eval
      rw [Finset.range_eq_Ico]
      symm
      refine Finset.sum_subset (Finset.Ico_subset_Ico (Nat.zero_le _) hbN) ?_
      intro i hi hni
      rw [Finset.mem_Ico] at hi hni
      rw [Set.indicator_of_notMem, zero_mul]
      intro hmem
      rcases Nat.lt_or_ge i (g.startIndex s) with h | h
      · have := (g.p_succ_le_of_lt_startIndex h).2
        exact absurd (hmem.2.trans this) (not_le.2 hσ.1)
      · have hbi : g.clampIndex t ≤ i := by omega
        have := g.le_p_of_clampIndex_le hbi hi.2
        exact absurd (hσ.2.trans this) (not_le.2 hmem.1)
    rw [hG, Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hlt := g.lt_of_lt_clampIndex (show g.startIndex s + j < g.clampIndex t by omega)
    have hind : (Set.Ioc (min (max (g.p (g.startIndex s + j)) s) t)
          (min (max (g.p (g.startIndex s + (j + 1))) s) t)).indicator (fun _ => (1 : ℝ)) σ
        = (Set.Ioc (g.p (g.startIndex s + j)) (g.p (g.startIndex s + j + 1))).indicator
          (fun _ => (1 : ℝ)) σ := by
      rw [← add_assoc]
      by_cases hmem : σ ∈ Set.Ioc (g.p (g.startIndex s + j)) (g.p (g.startIndex s + j + 1))
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem]
        exact ⟨min_lt_iff.2 (Or.inl (max_lt hmem.1 hσ.1)),
          le_min (le_max_of_le_left hmem.2) hσ.2⟩
      · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem]
        intro hmem'
        refine hmem ⟨?_, ?_⟩
        · rcases min_lt_iff.1 hmem'.1 with h | h
          · exact (max_lt_iff.1 h).1
          · exact absurd hσ.2 (not_le.2 h)
        · rcases le_max_iff.1 (le_min_iff.1 hmem'.2).1 with h | h
          · exact h
          · exact absurd h (not_le.2 hσ.1)
    have : ∑ k, (w ω * G.ξ (g.startIndex s + j) k ω) * (G.B k).indicator (fun _ => (1 : ℝ)) e
        = w ω * ∑ k, G.ξ (g.startIndex s + j) k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hind, this]
    ring
  · refine Finset.sum_eq_zero fun j _ => ?_
    rw [Set.indicator_of_notMem, zero_mul]
    intro hmem
    rcases not_and_or.1 hσ with h | h
    · exact h ((le_min (le_max_right _ _) hst.le).trans_lt hmem.1)
    · exact h (hmem.2.trans (min_le_right _ _))

/-- The integral of the weighted increment over its horizon, as a sum over the pieces
meeting `(s, t]`. -/
lemma full_incr_eq (ω : Ω) :
    (G.incr w hw hwm s t hs hst).full N ω
      = ∑ j ∈ Finset.range (g.clampIndex t - g.startIndex s),
        ∑ k, (w ω * G.ξ (g.startIndex s + j) k ω)
          * N.compensated (Set.Ioc (min (max (g.p (g.startIndex s + j)) s) t)
            (min (max (g.p (g.startIndex s + (j + 1))) s) t) ×ˢ G.B k) ω := by
  unfold full
  change ∑ i ∈ Finset.range (g.clampIndex t - g.startIndex s + 1),
      ∑ k, (if i = 0 then (0 : ℝ) else w ω * G.ξ (g.startIndex s + (i - 1)) k ω)
        * N.compensated (Set.Ioc ((g.incr s t hs hst).p i) ((g.incr s t hs hst).p (i + 1))
          ×ˢ G.B k) ω = _
  rw [Finset.sum_range_succ']
  simp only [ite_true, zero_mul, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [g.incr_p_succ, g.incr_p_succ]
  simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]

/-- The integral of the weighted increment over its horizon is the weighted increment of the
integral (almost surely: the piece containing `s` is split at `s`). -/
lemma full_incr :
    (fun ω => (G.incr w hw hwm s t hs hst).full N ω)
      =ᵐ[P] fun ω => w ω * (G.integral N t ω - G.integral N s ω) := by
  have hab : g.startIndex s ≤ g.clampIndex t := g.startIndex_le_clampIndex hs.le hst
  have hbN : g.clampIndex t ≤ g.N₀ := g.clampIndex_le t
  have hpa : g.p (g.startIndex s) ≤ s := g.p_startIndex_le hs.le
  have hinc : ∀ ω, G.integral N t ω - G.integral N s ω
      = ∑ i ∈ Finset.Ico (g.startIndex s) (g.clampIndex t), ∑ k, G.ξ i k ω
        * (N.compensated (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k) ω
          - N.compensated (Set.Ioc (min (g.p i) s) (min (g.p (i + 1)) s) ×ˢ G.B k) ω) := by
    intro ω
    unfold integral
    rw [← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib, ← mul_sub]
    rw [Finset.range_eq_Ico]
    symm
    refine Finset.sum_subset (Finset.Ico_subset_Ico (Nat.zero_le _) hbN) ?_
    intro i hi hni
    rw [Finset.mem_Ico] at hi hni
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases Nat.lt_or_ge i (g.startIndex s) with h | h
    · have h2 := (g.p_succ_le_of_lt_startIndex h).2
      have h1 : g.p i ≤ s := (g.p_mono (Nat.le_succ i) hi.2).trans h2
      rw [min_eq_left (h1.trans hst.le), min_eq_left (h2.trans hst.le), min_eq_left h1,
        min_eq_left h2, sub_self, mul_zero]
    · have hbi : g.clampIndex t ≤ i := by omega
      have hti := g.le_p_of_clampIndex_le hbi hi.2
      have hti' := hti.trans (g.p_mono (Nat.le_succ i) hi.2)
      rw [min_eq_right hti, min_eq_right hti', min_eq_right (hst.le.trans hti),
        min_eq_right (hst.le.trans hti'), compensated_Ioc_self, compensated_Ioc_self, sub_self,
        mul_zero]
  rcases Nat.lt_or_ge (g.startIndex s) g.N₀ with haN | haN
  · have hsa1 : s < g.p (g.startIndex s + 1) := g.lt_p_succ_startIndex haN
    have hsplit : ∀ᵐ ω ∂P, ∀ k : Fin G.K,
        N.compensated (Set.Ioc (g.p (g.startIndex s)) (min (g.p (g.startIndex s + 1)) t)
          ×ˢ G.B k) ω
          = N.compensated (Set.Ioc (g.p (g.startIndex s)) s ×ˢ G.B k) ω
            + N.compensated (Set.Ioc s (min (g.p (g.startIndex s + 1)) t) ×ˢ G.B k) ω := by
      rw [ae_all_iff]
      intro k
      exact compensated_Ioc_split N hpa (le_min hsa1.le hst.le) (G.B_measurable k)
        (G.B_finite k)
    filter_upwards [hsplit] with ω hω
    rw [full_incr_eq, hinc, Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hlt := g.lt_of_lt_clampIndex (show g.startIndex s + j < g.clampIndex t by omega)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← add_assoc]
    rcases Nat.eq_zero_or_pos j with hz | hz
    · subst hz
      simp only [add_zero]
      rw [max_eq_right hpa, min_eq_left hst.le, max_eq_left hsa1.le,
        min_eq_left (hpa.trans hst.le), min_eq_left hpa, min_eq_right hsa1.le, hω k]
      ring
    · have hgt : s < g.p (g.startIndex s + j) :=
      hsa1.trans_le (g.p_mono (by omega) hlt.1.le)
      have hgt' : s < g.p (g.startIndex s + j + 1) :=
        hgt.trans (g.p_lt _ hlt.1)
      rw [max_eq_left hgt.le, min_eq_left hlt.2.le, max_eq_left hgt'.le, min_eq_right hgt.le,
        min_eq_right hgt'.le, compensated_Ioc_self]
      ring
  · refine Filter.Eventually.of_forall fun ω => ?_
    beta_reduce
    rw [full_incr_eq, hinc]
    have h1 : g.clampIndex t - g.startIndex s = 0 := by omega
    have h2 : Finset.Ico (g.startIndex s) (g.clampIndex t) = ∅ :=
      Finset.Ico_eq_empty (not_lt.2 (by omega))
    rw [h1, h2]
    simp

include hw hwm hs hst in
include hℱ in
/-- The set-level `L²` isometry of the increment of the integral over `(s, t]` against a
bounded weight measurable at time `s`. -/
theorem integral_weight_incr_sq (hG : G.Adapted ℱ)
    (hwa : @StronglyMeasurable Ω ℝ _ (ℱ s) w) :
    ∫ ω, (w ω * (G.integral N t ω - G.integral N s ω)) ^ 2 ∂P
      = ∫ ω, (w ω) ^ 2 * (∫ e, ∫ σ in Set.Ioc s t, (G.eval σ e ω) ^ 2 ∂volume ∂ν) ∂P := by
  have key := (G.incr w hw hwm s t hs hst).integral_full_sq N hℱ (hG.incr hw hwm hs hst hwa)
    (g.incr_horizon_le s t hs hst)
  have hL : ∫ ω, ((G.incr w hw hwm s t hs hst).full N ω) ^ 2 ∂P
      = ∫ ω, (w ω * (G.integral N t ω - G.integral N s ω)) ^ 2 ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [full_incr N G hw hwm hs hst] with ω hω
    rw [hω]
  rw [← hL, key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  beta_reduce
  simp_rw [eval_incr]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  beta_reduce
  rw [← integral_const_mul]
  have hsub : Set.Ioc s t ⊆ Set.Icc 0 t := fun σ hσ => ⟨hs.le.trans hσ.1.le, hσ.2⟩
  rw [← Set.inter_eq_self_of_subset_right hsub, ← setIntegral_indicator measurableSet_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun σ _ => ?_
  by_cases hσ : σ ∈ Set.Ioc s t
  · rw [Set.indicator_of_mem hσ, ite_eq_left (Set.mem_Ioc.1 hσ)]
    ring
  · rw [Set.indicator_of_notMem hσ, ite_eq_right (fun h => hσ (Set.mem_Ioc.2 h))]
    ring

end Increment

end MarkStep

end LevyStochCalc.Poisson.Compensated
