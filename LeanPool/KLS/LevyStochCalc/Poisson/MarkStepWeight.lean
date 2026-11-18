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

public import LeanPool.KLS.LevyStochCalc.Poisson.MarkStepIsometry

/-!
# Sums, negations and weightings of mark-step integrands

Two mark-step integrands on a common time grid are added by concatenating their mark
families (`MarkStep.append`), and a mark-step integrand is negated coefficientwise
(`MarkStep.neg`); both operations act additively on the compensated integral and on the
integrand, so the `L²` isometry applies to differences. Multiplying the coefficients from a
given piece on by a bounded measurable weight `w`, and zeroing the earlier ones
(`MarkStep.weight`), yields the isometry for the weighted increment of the integral over a
grid interval.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

namespace MarkStep

section Append

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

/-- The sum of two mark-step integrands on a common grid, by concatenating their marks. -/
def append (G G' : MarkStep Ω E ν g) : MarkStep Ω E ν g where
  K := G.K + G'.K
  B := Fin.append G.B G'.B
  B_measurable := fun k => Fin.addCases (fun k => by
    simp only [Fin.append_left]; exact G.B_measurable k) (fun k => by
    simp only [Fin.append_right]; exact G'.B_measurable k) k
  B_finite := fun k => Fin.addCases (fun k => by
    simp only [Fin.append_left]; exact G.B_finite k) (fun k => by
    simp only [Fin.append_right]; exact G'.B_finite k) k
  ξ := fun i => Fin.append (G.ξ i) (G'.ξ i)
  ξ_bounded := fun i k => Fin.addCases (fun k => by
    simp only [Fin.append_left]; exact G.ξ_bounded i k) (fun k => by
    simp only [Fin.append_right]; exact G'.ξ_bounded i k) k
  ξ_measurable := fun i k => Fin.addCases (fun k => by
    simp only [Fin.append_left]; exact G.ξ_measurable i k) (fun k => by
    simp only [Fin.append_right]; exact G'.ξ_measurable i k) k

/-- The negative of a mark-step integrand. -/
def neg (G : MarkStep Ω E ν g) : MarkStep Ω E ν g where
  K := G.K
  B := G.B
  B_measurable := G.B_measurable
  B_finite := G.B_finite
  ξ := fun i k ω => -G.ξ i k ω
  ξ_bounded := fun i k => by
    obtain ⟨M, hM⟩ := G.ξ_bounded i k
    exact ⟨M, fun ω => by rw [abs_neg]; exact hM ω⟩
  ξ_measurable := fun i k => (G.ξ_measurable i k).neg

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G G' : MarkStep Ω E ν g)

lemma integral_append (t : ℝ) (ω : Ω) :
    (G.append G').integral N t ω = G.integral N t ω + G'.integral N t ω := by
  unfold integral
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  change ∑ k : Fin (G.K + G'.K), Fin.append (G.ξ i) (G'.ξ i) k ω
      * N.compensated (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t)
        ×ˢ Fin.append G.B G'.B k) ω = _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

lemma full_append (ω : Ω) : (G.append G').full N ω = G.full N ω + G'.full N ω := by
  unfold full
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  change ∑ k : Fin (G.K + G'.K), Fin.append (G.ξ i) (G'.ξ i) k ω
      * N.compensated (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ Fin.append G.B G'.B k) ω = _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

lemma eval_append (s : ℝ) (e : E) (ω : Ω) :
    (G.append G').eval s e ω = G.eval s e ω + G'.eval s e ω := by
  unfold eval
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_add]
  congr 1
  change ∑ k : Fin (G.K + G'.K), Fin.append (G.ξ i) (G'.ξ i) k ω
      * (Fin.append G.B G'.B k).indicator (fun _ => (1 : ℝ)) e = _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

lemma Adapted.append {G G' : MarkStep Ω E ν g}
    (hG : G.Adapted ℱ) (hG' : G'.Adapted ℱ) : (G.append G').Adapted ℱ := by
  intro i hi k
  refine Fin.addCases (fun k => ?_) (fun k => ?_) k
  · change @StronglyMeasurable Ω ℝ _ (ℱ (g.p i))
      (Fin.append (G.ξ i) (G'.ξ i) (Fin.castAdd _ k))
    rw [Fin.append_left]
    exact hG i hi k
  · change @StronglyMeasurable Ω ℝ _ (ℱ (g.p i))
      (Fin.append (G.ξ i) (G'.ξ i) (Fin.natAdd _ k))
    rw [Fin.append_right]
    exact hG' i hi k

lemma integral_neg (t : ℝ) (ω : Ω) : G.neg.integral N t ω = -G.integral N t ω := by
  unfold integral
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  change -G.ξ i k ω * N.compensated (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k) ω
    = -(G.ξ i k ω * N.compensated (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k) ω)
  exact neg_mul _ _

lemma full_neg (ω : Ω) : G.neg.full N ω = -G.full N ω := by
  unfold full
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  change -G.ξ i k ω * N.compensated (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) ω
    = -(G.ξ i k ω * N.compensated (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) ω)
  exact neg_mul _ _

lemma eval_neg (s : ℝ) (e : E) (ω : Ω) : G.neg.eval s e ω = -G.eval s e ω := by
  unfold eval
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  change -G.ξ i k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e
    = -(G.ξ i k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e)
  exact neg_mul _ _

lemma Adapted.neg {G : MarkStep Ω E ν g} (hG : G.Adapted ℱ) :
    G.neg.Adapted ℱ := fun i hi k => (hG i hi k).neg

include hℱ in
/-- The `L²` distance of the compensated integrals of two adapted mark-step integrands on
a common grid, up to time `t ≥ 0`, is the `L²` distance of the integrands. -/
theorem integral_sub_sq_at (hG : G.Adapted ℱ) (hG' : G'.Adapted ℱ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, (G.integral N t ω - G'.integral N t ω) ^ 2 ∂P
      = ∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) t,
          (G.eval s e ω - G'.eval s e ω) ^ 2 ∂volume ∂ν) ∂P := by
  have key := (G.append G'.neg).integral_sq_at N hℱ (hG.append hG'.neg) ht
  simp only [integral_append, integral_neg, eval_append, eval_neg, ← sub_eq_add_neg] at key
  exact key

include hℱ in
/-- The `L²` distance of the compensated integrals of two adapted mark-step integrands on
a common grid, up to time `t ≥ 0`, in `ℝ≥0∞` form. -/
theorem lintegral_integral_sub_sq_at (hG : G.Adapted ℱ) (hG' : G'.Adapted ℱ) {t : ℝ}
    (ht : 0 ≤ t) :
    ∫⁻ ω, (‖G.integral N t ω - G'.integral N t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖G.eval s e ω - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂ν ∂P := by
  have key := (G.append G'.neg).lintegral_integral_sq_at N hℱ (hG.append hG'.neg) ht
  simp only [integral_append, integral_neg, eval_append, eval_neg, ← sub_eq_add_neg] at key
  exact key

end Append

section Weight

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

/-- The mark-step integrand whose coefficients on the pieces from index `a` on are
multiplied by a bounded measurable weight `w`, and whose earlier coefficients vanish. -/
def weight (G : MarkStep Ω E ν g) (w : Ω → ℝ) (hw : ∃ C : ℝ, ∀ ω, |w ω| ≤ C)
    (hwm : Measurable w) (a : ℕ) : MarkStep Ω E ν g where
  K := G.K
  B := G.B
  B_measurable := G.B_measurable
  B_finite := G.B_finite
  ξ := fun i k ω => if a ≤ i then w ω * G.ξ i k ω else 0
  ξ_bounded := fun i k => by
    obtain ⟨C, hC⟩ := hw
    obtain ⟨M, hM⟩ := G.ξ_bounded i k
    refine ⟨|C| * |M|, fun ω => ?_⟩
    split_ifs
    · rw [abs_mul]
      exact mul_le_mul ((hC ω).trans (le_abs_self C)) ((hM ω).trans (le_abs_self M))
        (abs_nonneg _) (abs_nonneg _)
    · rw [abs_zero]
      positivity
  ξ_measurable := fun i k => by
    by_cases h : a ≤ i
    · simp only [h, ite_true]
      exact hwm.mul (G.ξ_measurable i k)
    · simp only [h, ite_false]
      exact measurable_const

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G : MarkStep Ω E ν g) {w : Ω → ℝ}
  (hw : ∃ C : ℝ, ∀ ω, |w ω| ≤ C) (hwm : Measurable w)

include hw hwm in
lemma Adapted.weight {G : MarkStep Ω E ν g} (hG : G.Adapted ℱ)
    {a : ℕ} (hwa : @StronglyMeasurable Ω ℝ _ (ℱ (g.p a)) w) :
    (G.weight w hw hwm a).Adapted ℱ := by
  intro i hi k
  change @StronglyMeasurable Ω ℝ _ (ℱ (g.p i))
    (fun ω => if a ≤ i then w ω * G.ξ i k ω else 0)
  by_cases h : a ≤ i
  · simp only [h, ite_true]
    exact (hwa.mono (ℱ.mono (g.p_mono h hi.le))).mul (hG i hi k)
  · simp only [h, ite_false]
    exact stronglyMeasurable_const

/-- The integral of a mark-step integrand up to a grid point, as a sum over the pieces
before it. -/
lemma integral_p_eq (b : ℕ) (hb : b ≤ g.N₀) (ω : Ω) :
    G.integral N (g.p b) ω = ∑ i ∈ Finset.range b, ∑ k, G.ξ i k ω
      * N.compensated (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) ω := by
  unfold integral
  refine (Finset.sum_subset (Finset.range_subset.2 fun i hi =>
    Finset.mem_range.2 (lt_of_lt_of_le hi hb)) ?_).symm.trans
    (Finset.sum_congr rfl fun i hi => ?_)
  · intro i hi hni
    rw [Finset.mem_range] at hi hni
    have hti : g.p b ≤ g.p i := g.p_mono (not_lt.1 hni) hi.le
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [min_eq_right hti, min_eq_right (hti.trans (g.p_mono (Nat.le_succ i) hi)),
      compensated_Ioc_self, mul_zero]
  · rw [Finset.mem_range] at hi
    rw [min_eq_left (g.p_mono hi.le hb), min_eq_left (g.p_mono hi hb)]

/-- The weighted increment of the integral between two grid points, as the integral of
the weighted integrand over the clamped horizon. -/
lemma full_weight_clamp {a b : ℕ} (hab : a ≤ b) (hb : b ≤ g.N₀) (ω : Ω) :
    ((G.clamp (g.p b) (g.p_nonneg hb)).weight w hw hwm a).full N ω
      = w ω * (G.integral N (g.p b) ω - G.integral N (g.p a) ω) := by
  rw [G.integral_p_eq N b hb, G.integral_p_eq N a (hab.trans hb)]
  have hN : (g.clamp (g.p b) (g.p_nonneg hb)).N₀ = b := g.clampIndex_p hb
  unfold full
  rw [hN]
  change ∑ i ∈ Finset.range b, ∑ k, (if a ≤ i then w ω * G.ξ i k ω else 0)
      * N.compensated (Set.Ioc (min (g.p i) (g.p b)) (min (g.p (i + 1)) (g.p b)) ×ˢ G.B k) ω
    = _
  set F : ℕ → ℝ := fun i => ∑ k, G.ξ i k ω
    * N.compensated (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) ω with hF
  have hL : ∀ i ∈ Finset.range b, (∑ k, (if a ≤ i then w ω * G.ξ i k ω else 0)
      * N.compensated (Set.Ioc (min (g.p i) (g.p b)) (min (g.p (i + 1)) (g.p b)) ×ˢ G.B k) ω)
      = if a ≤ i then w ω * F i else 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [min_eq_left (g.p_mono hi.le hb), min_eq_left (g.p_mono hi hb), hF]
    split_ifs
    · simp only [Finset.mul_sum, mul_assoc]
    · simp
  rw [Finset.sum_congr rfl hL]
  have h2 : ∑ i ∈ Finset.range b, (if a ≤ i then 0 else w ω * F i)
      = ∑ i ∈ Finset.range a, w ω * F i := by
    refine (Finset.sum_subset (Finset.range_subset.2 fun i hi =>
      Finset.mem_range.2 (lt_of_lt_of_le hi hab)) ?_).symm.trans
      (Finset.sum_congr rfl fun i hi => ?_)
    · intro i hi hni
      rw [Finset.mem_range] at hni
      simp [not_lt.1 hni]
    · rw [Finset.mem_range] at hi
      simp [not_le.2 hi]
  have hsplit : ∑ i ∈ Finset.range b, (if a ≤ i then w ω * F i else 0)
      + ∑ i ∈ Finset.range a, w ω * F i = ∑ i ∈ Finset.range b, w ω * F i := by
    rw [← h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  linarith [hsplit]

/-- The integrand of the weighted clamped integrand. -/
lemma eval_weight_clamp {a b : ℕ} (hab : a ≤ b) (hb : b ≤ g.N₀) (s : ℝ) (e : E) (ω : Ω) :
    ((G.clamp (g.p b) (g.p_nonneg hb)).weight w hw hwm a).eval s e ω
      = if g.p a < s ∧ s ≤ g.p b then w ω * G.eval s e ω else 0 := by
  have hN : (g.clamp (g.p b) (g.p_nonneg hb)).N₀ = b := g.clampIndex_p hb
  have hL : ((G.clamp (g.p b) (g.p_nonneg hb)).weight w hw hwm a).eval s e ω
      = ∑ i ∈ Finset.range b, (Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) s
        * ∑ k, (if a ≤ i then w ω * G.ξ i k ω else 0)
          * (G.B k).indicator (fun _ => (1 : ℝ)) e := by
    unfold eval
    rw [hN]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    change (Set.Ioc (min (g.p i) (g.p b)) (min (g.p (i + 1)) (g.p b))).indicator
        (fun _ => (1 : ℝ)) s * _ = _
    rw [min_eq_left (g.p_mono hi.le hb), min_eq_left (g.p_mono hi hb)]
    rfl
  rw [hL]
  split_ifs with hs
  · unfold eval
    rw [Finset.mul_sum]
    refine (Finset.sum_congr rfl fun i hi => ?_).trans (Finset.sum_subset
      (Finset.range_subset.2 fun i hi => Finset.mem_range.2 (lt_of_lt_of_le hi hb)) ?_)
    · rw [Finset.mem_range] at hi
      by_cases hai : a ≤ i
      · simp only [hai, ite_true, Finset.mul_sum, mul_assoc]
        ring_nf
      · have hs0 : s ∉ Set.Ioc (g.p i) (g.p (i + 1)) := fun hs' =>
          absurd (hs'.2.trans (g.p_mono (Nat.succ_le_of_lt (not_le.1 hai)) (hab.trans hb)))
            (not_le.2 hs.1)
        rw [Set.indicator_of_notMem hs0]
        simp
    · intro i hi hni
      rw [Finset.mem_range] at hi hni
      rw [Set.indicator_of_notMem, zero_mul, mul_zero]
      intro hs'
      exact absurd (hs.2.trans (g.p_mono (not_lt.1 hni) hi.le)) (not_le.2 hs'.1)
  · refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_range] at hi
    by_cases hai : a ≤ i
    · rw [Set.indicator_of_notMem, zero_mul]
      intro hs'
      exact hs ⟨(g.p_mono hai (hi.le.trans hb)).trans_lt hs'.1, hs'.2.trans (g.p_mono hi hb)⟩
    · simp [hai]

include hℱ in
/-- The set-level `L²` isometry of the increment of the integral between two grid points,
against a bounded weight measurable at the earlier grid point. -/
theorem integral_weight_increment_sq (hG : G.Adapted ℱ) {w : Ω → ℝ}
    (hw : ∃ C : ℝ, ∀ ω, |w ω| ≤ C) (hwm : Measurable w) {a b : ℕ} (hab : a ≤ b)
    (hb : b ≤ g.N₀)
    (hwa : @StronglyMeasurable Ω ℝ _ (ℱ (g.p a)) w) :
    ∫ ω, (w ω * (G.integral N (g.p b) ω - G.integral N (g.p a) ω)) ^ 2 ∂P
      = ∫ ω, (w ω) ^ 2 * (∫ e, ∫ s in Set.Ioc (g.p a) (g.p b),
          (G.eval s e ω) ^ 2 ∂volume ∂ν) ∂P := by
  have hb0 := g.p_nonneg hb
  have hwa' : @StronglyMeasurable Ω ℝ _ (ℱ ((g.clamp (g.p b) hb0).p a)) w := by
    change @StronglyMeasurable Ω ℝ _ (ℱ (min (g.p a) (g.p b))) w
    rwa [min_eq_left (g.p_mono hab hb)]
  have key := ((G.clamp (g.p b) hb0).weight w hw hwm a).integral_full_sq N hℱ
    ((hG.clamp (g.p b) hb0).weight hw hwm hwa') (g.clamp_horizon_le (g.p b) hb0)
  simp_rw [G.full_weight_clamp N hw hwm hab hb, G.eval_weight_clamp hw hwm hab hb] at key
  rw [key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  beta_reduce
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  beta_reduce
  rw [← integral_const_mul]
  have hsub : Set.Ioc (g.p a) (g.p b) ⊆ Set.Icc 0 (g.p b) := fun s hs =>
    ⟨(g.p_nonneg (hab.trans hb)).trans hs.1.le, hs.2⟩
  rw [← Set.inter_eq_self_of_subset_right hsub, ← setIntegral_indicator measurableSet_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun s _ => ?_
  by_cases hs : s ∈ Set.Ioc (g.p a) (g.p b)
  · rw [Set.indicator_of_mem hs, ite_eq_left (Set.mem_Ioc.1 hs)]
    ring
  · rw [Set.indicator_of_notMem hs, ite_eq_right (fun h => hs (Set.mem_Ioc.2 h))]
    ring

/-- The weighted integrand from index `0`: every coefficient is multiplied by `w`. -/
lemma full_weight_zero (ω : Ω) : (G.weight w hw hwm 0).full N ω = w ω * G.full N ω := by
  unfold full
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  change (if 0 ≤ i then w ω * G.ξ i k ω else 0) * _ = _
  rw [ite_eq_left (Nat.zero_le i), mul_assoc]
  rfl

/-- The integrand of the integrand weighted from index `0`. -/
lemma eval_weight_zero (s : ℝ) (e : E) (ω : Ω) :
    (G.weight w hw hwm 0).eval s e ω = w ω * G.eval s e ω := by
  unfold eval
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change (Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) s
      * ∑ k : Fin G.K, (if 0 ≤ i then w ω * G.ξ i k ω else 0)
        * (G.B k).indicator (fun _ => (1 : ℝ)) e
    = w ω * ((Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) s
      * ∑ k : Fin G.K, G.ξ i k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e)
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ite_eq_left (Nat.zero_le i)]
  ring

include hw hwm in
include hℱ in
/-- The set-level `L²` isometry of the integral up to time `t ≥ 0` against a bounded weight
measurable at time `0`. -/
theorem integral_weight_zero_sq (hG : G.Adapted ℱ) {t : ℝ} (ht : 0 ≤ t)
    (hwa : @StronglyMeasurable Ω ℝ _ (ℱ 0) w) :
    ∫ ω, (w ω * G.integral N t ω) ^ 2 ∂P
      = ∫ ω, (w ω) ^ 2 * (∫ e, ∫ s in Set.Icc (0 : ℝ) t,
          (G.eval s e ω) ^ 2 ∂volume ∂ν) ∂P := by
  have hwa' : @StronglyMeasurable Ω ℝ _ (ℱ ((g.clamp t ht).p 0)) w := by
    change @StronglyMeasurable Ω ℝ _ (ℱ (min (g.p 0) t)) w
    rwa [g.p_zero, min_eq_left ht]
  have key := ((G.clamp t ht).weight w hw hwm 0).integral_full_sq N hℱ
    ((hG.clamp t ht).weight hw hwm hwa') (g.clamp_horizon_le t ht)
  simp_rw [(G.clamp t ht).full_weight_zero N hw hwm, (G.clamp t ht).eval_weight_zero hw hwm,
    ← G.integral_eq_full_clamp N t ht, G.eval_clamp t ht] at key
  rw [key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  beta_reduce
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  beta_reduce
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  rw [ite_eq_left hs.2]
  ring

end Weight

end MarkStep

end LevyStochCalc.Poisson.Compensated
