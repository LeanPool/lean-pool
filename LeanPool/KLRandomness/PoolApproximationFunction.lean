/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.PoolApproximation
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite-prefix approximation in L1

Real integrable functions on Cantor space are approximated in L1 by finite
tables.  Rational tables suffice, and the approximants can stay in `[0,1]`
when the target function has that range.
-/

@[expose] public section

namespace Klr.PoolApproximation

open MeasureTheory Filter
open scoped ENNReal symmDiff Topology

theorem integrable_eval {d : ℕ} (table : (Fin d → Bool) → ℝ) :
    Integrable (eval table) fairCoin := by
  exact (Integrable.of_finite (μ := Measure.map (bits d) fairCoin) (f := table)).comp_measurable
    (measurable_prefix d)

/-- The L1 error obeys the triangle inequality. -/
theorem integral_norm_sub_triangle {f g h : Cantor → ℝ}
    (hf : Integrable f fairCoin) (hg : Integrable g fairCoin) (hh : Integrable h fairCoin) :
    (∫ X, ‖f X - h X‖ ∂fairCoin) ≤
      (∫ X, ‖f X - g X‖ ∂fairCoin) + ∫ X, ‖g X - h X‖ ∂fairCoin := by
  calc
    _ ≤ ∫ X, ‖f X - g X‖ + ‖g X - h X‖ ∂fairCoin := by
      apply integral_mono (hf.sub hh).norm ((hf.sub hg).norm.add (hg.sub hh).norm)
      intro X
      simpa only [Pi.sub_apply, Pi.add_apply, dist_eq_norm] using dist_triangle (f X) (g X) (h X)
    _ = _ := integral_add (hf.sub hg).norm (hg.sub hh).norm

/-- Indicator error is precisely the measure of the symmetric difference,
multiplied by the size of the coefficient. -/
theorem integral_norm_indicator_sub_indicator {s t : Set Cantor}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (c : ℝ) :
    (∫ X, ‖s.indicator (fun _ => c) X - t.indicator (fun _ => c) X‖ ∂fairCoin) =
      fairCoin.real (s ∆ t) * ‖c‖ := by
  classical
  calc
    _ = ∫ X, (s ∆ t).indicator (fun _ => ‖c‖) X ∂fairCoin := by
      apply integral_congr_ae
      filter_upwards with X
      by_cases hXs : X ∈ s <;> by_cases hXt : X ∈ t <;>
        simp [Set.indicator, Set.mem_symmDiff, hXs, hXt]
    _ = _ := by simpa using integral_indicator_const (μ := fairCoin) ‖c‖ (hs.symmDiff ht)

/-- A scalar indicator can be approximated by a real prefix table. -/
theorem exists_realTable_indicator {H : Set Cantor} (hH : MeasurableSet H) (c : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (d : ℕ) (table : (Fin d → Bool) → ℝ),
      (∫ X, ‖eval table X - H.indicator (fun _ => c) X‖ ∂fairCoin) < ε := by
  classical
  obtain ⟨d, table, ht⟩ := exists_event_measureReal_symmDiff_lt hH
    (show 0 < ε / (‖c‖ + 1) by positivity)
  refine ⟨d, fun u => if table u then c else 0, ?_⟩
  have he : eval (fun u => if table u then c else 0) =
      (event table).indicator (fun _ => c) := by
    funext X
    simp only [eval, event, Set.indicator, Set.mem_ofPred]
  rw [he, integral_norm_indicator_sub_indicator (measurableSet_event table) hH]
  calc
    _ ≤ fairCoin.real (event table ∆ H) * (‖c‖ + 1) := by
      gcongr
      linarith
    _ < (ε / (‖c‖ + 1)) * (‖c‖ + 1) :=
      mul_lt_mul_of_pos_right ht (by positivity)
    _ = ε := div_mul_cancel₀ ε (by positivity)

/-- Every measurable simple real function admits finite-prefix L1 approximations. -/
theorem exists_realTable_simpleFunc (f : SimpleFunc Cantor ℝ) :
    ∀ (ε : ℝ), 0 < ε → ∃ (d : ℕ) (table : (Fin d → Bool) → ℝ),
      (∫ X, ‖eval table X - f X‖ ∂fairCoin) < ε := by
  classical
  induction f using SimpleFunc.induction with
  | const c hH =>
    intro ε hε
    simpa only [SimpleFunc.piecewise_apply, SimpleFunc.const_apply, Set.indicator] using
      exists_realTable_indicator hH c hε
  | @add f g _ hf hg =>
    intro ε hε
    obtain ⟨d, a, ha⟩ := hf (ε / 2) (half_pos hε)
    obtain ⟨e, b, hb⟩ := hg (ε / 2) (half_pos hε)
    let table : (Fin (max d e) → Bool) → ℝ := fun u =>
      liftTable (Nat.le_max_left d e) a u + liftTable (Nat.le_max_right d e) b u
    refine ⟨max d e, table, ?_⟩
    have hpoint (X : Cantor) :
        ‖eval table X - (f + g) X‖ ≤ ‖eval a X - f X‖ + ‖eval b X - g X‖ := by
      have he : eval table X - (f + g) X =
          (eval a X - f X) + (eval b X - g X) := by
        change (eval a X + eval b X) - (f X + g X) = _
        ring
      rw [he]
      exact norm_add_le _ _
    calc
      _ ≤ ∫ X, ‖eval a X - f X‖ + ‖eval b X - g X‖ ∂fairCoin := by
        exact integral_mono
          ((integrable_eval table).sub (f + g).integrable_of_isFiniteMeasure).norm
          (((integrable_eval a).sub f.integrable_of_isFiniteMeasure).norm.add
            ((integrable_eval b).sub g.integrable_of_isFiniteMeasure).norm) hpoint
      _ = (∫ X, ‖eval a X - f X‖ ∂fairCoin) + ∫ X, ‖eval b X - g X‖ ∂fairCoin :=
        integral_add ((integrable_eval a).sub f.integrable_of_isFiniteMeasure).norm
          ((integrable_eval b).sub g.integrable_of_isFiniteMeasure).norm
      _ < ε := by linarith

/-- Finite real prefix tables are dense in the real integrable functions. -/
theorem exists_realTable_integral_norm_sub_lt {f : Cantor → ℝ}
    (hfm : Measurable f) (hf : Integrable f fairCoin) {ε : ℝ} (hε : 0 < ε) :
    ∃ (d : ℕ) (table : (Fin d → Bool) → ℝ),
      (∫ X, ‖eval table X - f X‖ ∂fairCoin) < ε := by
  obtain ⟨n, hn⟩ := ((tendsto_integral_norm_approxOn_sub hfm hf).eventually
    (gt_mem_nhds (half_pos hε))).exists
  let g : SimpleFunc Cantor ℝ := SimpleFunc.approxOn f hfm (Set.range f ∪ {0}) 0 (by simp) n
  obtain ⟨d, table, ht⟩ := exists_realTable_simpleFunc g (ε / 2) (half_pos hε)
  refine ⟨d, table, ?_⟩
  have htriangle := integral_norm_sub_triangle (integrable_eval table)
    g.integrable_of_isFiniteMeasure hf
  have hgn : (∫ X, ‖g X - f X‖ ∂fairCoin) < ε / 2 := hn
  linarith

/-- A finite real table has a uniformly close rational table. -/
theorem exists_ratTable_uniform_lt {d : ℕ} (table : (Fin d → Bool) → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : (Fin d → Bool) → ℚ, ∀ u, ‖(q u : ℝ) - table u‖ < ε := by
  have h (u : Fin d → Bool) : ∃ q : ℚ, ‖(q : ℝ) - table u‖ < ε := by
    obtain ⟨q, hlo, hhi⟩ := exists_rat_btwn
      (show table u - ε < table u + ε by linarith)
    refine ⟨q, ?_⟩
    rw [Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  choose q hq using h
  exact ⟨q, hq⟩

/-- Rational-valued finite tables are dense in L1 on fair-coin Cantor space. -/
theorem exists_ratTable_integral_norm_sub_lt {f : Cantor → ℝ}
    (hfm : Measurable f) (hf : Integrable f fairCoin) {ε : ℝ} (hε : 0 < ε) :
    ∃ (d : ℕ) (table : (Fin d → Bool) → ℚ),
      (∫ X, ‖((eval table X : ℚ) : ℝ) - f X‖ ∂fairCoin) < ε := by
  obtain ⟨d, table, ht⟩ := exists_realTable_integral_norm_sub_lt hfm hf (half_pos hε)
  obtain ⟨q, hq⟩ := exists_ratTable_uniform_lt table (half_pos hε)
  have hiq := integrable_eval (fun u => (q u : ℝ))
  have hqint : (∫ X, ‖((eval q X : ℚ) : ℝ) - eval table X‖ ∂fairCoin) ≤ ε / 2 := by
    calc
      _ ≤ ∫ _ : Cantor, ε / 2 ∂fairCoin := by
        apply integral_mono (hiq.sub (integrable_eval table)).norm (integrable_const _)
        intro X
        exact (hq (bits d X)).le
      _ = ε / 2 := by simp
  refine ⟨d, q, ?_⟩
  have htriangle := integral_norm_sub_triangle hiq (integrable_eval table) hf
  simp only [eval] at htriangle hqint ht ⊢
  linarith

/-- Clipping to the unit interval cannot increase error against a point in that interval. -/
theorem norm_clip_sub_le (a b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ‖min 1 (max 0 a) - b‖ ≤ ‖a - b‖ := by
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  by_cases ha0 : a ≤ 0
  · rw [max_eq_left ha0, min_eq_right (by norm_num : (0 : ℝ) ≤ 1), zero_sub, abs_neg,
      abs_of_nonneg hb0, abs_of_nonpos (by linarith : a - b ≤ 0)]
    linarith
  · rw [max_eq_right (le_of_lt (lt_of_not_ge ha0))]
    by_cases ha1 : 1 ≤ a
    · rw [min_eq_left ha1, abs_of_nonneg (by linarith : 0 ≤ 1 - b),
        abs_of_nonneg (by linarith : 0 ≤ a - b)]
      linarith
    · rw [min_eq_right (le_of_lt (lt_of_not_ge ha1))]

/-- A measurable `[0,1]`-valued target admits a fixed rational prefix table,
also valued in `[0,1]`, with arbitrarily small L1 error. -/
theorem exists_unitRatTable_integral_norm_sub_lt {f : Cantor → ℝ}
    (hfm : Measurable f) (hf0 : ∀ X, 0 ≤ f X) (hf1 : ∀ X, f X ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (d : ℕ) (table : (Fin d → Bool) → ℚ),
      (∀ u, 0 ≤ table u ∧ table u ≤ 1) ∧
      (∫ X, ‖((eval table X : ℚ) : ℝ) - f X‖ ∂fairCoin) < ε := by
  have hf : Integrable f fairCoin := Integrable.of_bound hfm.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 X)]
      exact hf1 X)
  obtain ⟨d, table, ht⟩ := exists_ratTable_integral_norm_sub_lt hfm hf hε
  let q : (Fin d → Bool) → ℚ := fun u => min 1 (max 0 (table u))
  refine ⟨d, q, ?_, ?_⟩
  · intro u
    exact ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩
  · calc
      _ ≤ ∫ X, ‖((eval table X : ℚ) : ℝ) - f X‖ ∂fairCoin := by
        apply integral_mono ((integrable_eval (fun u => (q u : ℝ))).sub hf).norm
          ((integrable_eval (fun u => (table u : ℝ))).sub hf).norm
        intro X
        simpa only [eval, q, Rat.cast_min, Rat.cast_max, Rat.cast_one, Rat.cast_zero,
          Pi.sub_apply] using norm_clip_sub_le ((eval table X : ℚ) : ℝ) (f X) (hf0 X) (hf1 X)
      _ < ε := ht

/-- A finite family of Borel events and unit-interval functions has simultaneous
approximations at one common depth.  All the tables are fixed before a later
affine block or its dimension is selected. -/
theorem exists_common_tables {ι : Type*} [Finite ι]
    (H : ι → Set Cantor) (hH : ∀ i, MeasurableSet (H i))
    (f : ι → Cantor → ℝ) (hfm : ∀ i, Measurable (f i))
    (hf0 : ∀ i X, 0 ≤ f i X) (hf1 : ∀ i X, f i X ≤ 1)
    {εH εf : ℝ} (hεH : 0 < εH) (hεf : 0 < εf) :
    ∃ (d : ℕ) (high : ι → (Fin d → Bool) → Bool) (value : ι → (Fin d → Bool) → ℚ),
      ∀ i, fairCoin.real (event (high i) ∆ H i) < εH ∧
        (∀ u, 0 ≤ value i u ∧ value i u ≤ 1) ∧
        (∫ X, ‖((eval (value i) X : ℚ) : ℝ) - f i X‖ ∂fairCoin) < εf := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose dH high hhigh using fun i => exists_event_measureReal_symmDiff_lt (hH i) hεH
  choose df value hvalue herror using fun i =>
    exists_unitRatTable_integral_norm_sub_lt (hfm i) (hf0 i) (hf1 i) hεf
  let d := max (Finset.univ.sup dH) (Finset.univ.sup df)
  have hHd (i : ι) : dH i ≤ d :=
    (Finset.le_sup (f := dH) (Finset.mem_univ i)).trans (Nat.le_max_left _ _)
  have hfd (i : ι) : df i ≤ d :=
    (Finset.le_sup (f := df) (Finset.mem_univ i)).trans (Nat.le_max_right _ _)
  refine ⟨d, fun i => liftTable (hHd i) (high i),
    fun i => liftTable (hfd i) (value i), ?_⟩
  intro i
  refine ⟨?_, ?_, ?_⟩
  · simpa only [event_liftTable] using hhigh i
  · intro u
    exact hvalue i (fun j => u (Fin.castLE (hfd i) j))
  · simpa only [eval_liftTable] using herror i

end Klr.PoolApproximation
