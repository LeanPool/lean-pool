/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianContinuousClosedStopping.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticContinuousStoppingTime
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! Genuine closed-set first hitting times of continuous adapted paths. -/

@[expose] public section
open Set MeasureTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreContinuous_closed_exit_isStoppingTime {Ω E : Type*} [mAmbient : MeasurableSpace Ω]
    [MetricSpace E]
    (F : Filtration ℝ≥0 mAmbient) (u : ℝ≥0 → Ω → E)
    (huA : StronglyAdapted F u) (huC : ∀ ω, Continuous (fun t => u t ω))
    (S : Set E) (hS : IsClosed S) (T : ℝ≥0) :
    IsStoppingTime F (fun ω => ((hittingBtwn u S 0 T ω : ℝ≥0) : WithTop ℝ≥0)) := by
  classical
  by_cases hne : S.Nonempty
  · let f : E → ℝ := fun x => Real.exp (-Metric.infDist x S)
    have hf : Continuous f := Real.continuous_exp.comp (Metric.continuous_infDist_pt S).neg
    have hmem (x : E) : x ∈ S ↔ 1 ≤ ‖f x‖ := by
      rw [hS.mem_iff_infDist_zero hne]
      change Metric.infDist x S = 0 ↔ 1 ≤ ‖Real.exp (-Metric.infDist x S)‖
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.one_le_exp_iff]
      constructor
      · intro h; simp [h]
      · intro h; linarith [Metric.infDist_nonneg (x := x) (s := S)]
    let v : ℝ≥0 → Ω → ℝ := fun t ω => f (u t ω)
    have hvA : StronglyAdapted F v := fun t => hf.comp_stronglyMeasurable (huA t)
    have hvC (ω : Ω) : Continuous (fun t => v t ω) := hf.comp (huC ω)
    have hstop := ginibreContinuous_norm_exit_isStoppingTime F v hvA hvC 1 T
    have he : hittingBtwn u S 0 T = hittingBtwn v {x | (1 : ℝ) ≤ ‖x‖} 0 T := by
      funext ω
      unfold hittingBtwn
      simp only [v, Set.mem_ofPred_eq]
      simp_rw [← hmem]
    simpa only [he] using hstop
  · have he : S = ∅ := not_nonempty_iff_eq_empty.mp hne
    subst S
    intro t
    simp only [hittingBtwn, Set.mem_empty_iff_false, exists_false, and_false,
      ↓reduceIte, WithTop.coe_le_coe]
    exact MeasurableSet.const _

theorem ginibreContinuous_mem_closure_until_exit {Ω E : Type*} [TopologicalSpace E]
    (u : ℝ≥0 → Ω → E) (G : Set E) (T : ℝ≥0) (ω : Ω)
    (hu : Continuous (fun t => u t ω)) (h0 : u 0 ω ∈ G)
    (t : ℝ≥0) (ht : t ≤ hittingBtwn u Gᶜ 0 T ω) : u t ω ∈ closure G := by
  classical
  by_cases hzero : t=0
  · subst t
    exact subset_closure h0
  have htpos : (0 : ℝ)<t := by exact_mod_cast (pos_iff_ne_zero.mpr hzero)
  have hq : ∀ k : ℕ, ∃ q : ℚ,
      max 0 ((t : ℝ)-1/((k : ℝ)+1))<(q : ℝ) ∧ (q : ℝ)<t := by
    intro k
    apply exists_rat_btwn
    apply max_lt htpos
    have he : (0 : ℝ)<1/((k : ℝ)+1) := by positivity
    linarith
  choose q hq using hq
  have hqpos (k : ℕ) : (0 : ℝ)≤q k :=
    ((le_max_left 0 ((t : ℝ)-1/((k : ℝ)+1))).trans_lt (hq k).1).le
  have hseq : Tendsto (fun k => (q k : ℝ).toNNReal) atTop (𝓝 t) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun k => dist_nonneg) _ (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    intro k
    rw [NNReal.dist_eq, Real.coe_toNNReal _ (hqpos k), abs_of_nonpos (sub_nonpos.mpr (hq k).2.le)]
    have hh := le_max_right 0 ((t : ℝ)-1/((k : ℝ)+1))
    linarith [(hq k).1]
  apply isClosed_closure.mem_of_tendsto (hu.tendsto t |>.comp hseq)
  apply Eventually.of_forall
  intro k
  apply subset_closure
  have hqtime : (q k : ℝ).toNNReal < t := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (hqpos k)]
    exact (hq k).2
  by_contra hn
  have hh : u (q k : ℝ).toNNReal ω ∈ Gᶜ := hn
  have hstop := hittingBtwn_le_of_mem (u := u) (s := Gᶜ) (n := 0) (m := T)
    (i := (q k : ℝ).toNNReal) (ω := ω) (bot_le : (0 : ℝ≥0) ≤ (q k : ℝ).toNNReal)
    ((hqtime.le.trans ht).trans (hittingBtwn_le ω)) hh
  exact not_lt_of_ge (ht.trans hstop) hqtime

end
end GinibrePoincare
