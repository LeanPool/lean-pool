/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralHorizonComparison.lean.
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

public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoIntervalRefinementGeometry
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralIntervalConvergence

/-!
# Ginibre Brownian integral horizon comparison

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianUniformPartialSum_horizon_difference_tendsto_meanSquare`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem brownianUniformPartialSum_horizon_difference_tendsto_meanSquare
    {Ω ι : Type*} [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F t))
    (hFi : ∀ t, MemLp (F t) 2 P) (T t : ℝ≥0) (ht : t ≤ T)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun s => F s ω) (Set.Icc 0 T))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ s ω, ‖F s ω‖ ≤ C) :
    Tendsto (fun n => ∫ ω,
      (brownianUniformPartialSum (B j) F T (n+1) t ω-
        brownianUniformLeftSum (B j) F t (n+1) ω)^2 ∂P) atTop (𝓝 0) := by
  have := Fintype.ofFinite ι
  classical
  let κ := fun n : ℕ => Fin (n+1) × Fin (n+1)
  let s : (n : ℕ) → κ n → ℝ≥0 := fun n k =>
    itoHorizonIntersectionStart T t (n+1) (n+1) k.1 k.2
  let e : (n : ℕ) → κ n → ℝ≥0 := fun n k =>
    itoHorizonIntersectionEnd T t (n+1) (n+1) k.1 k.2
  let d : (n : ℕ) → κ n → ℝ≥0 := fun n k => e n k-s n k
  have hse : ∀ n k, s n k ≤ e n k := fun n k => le_max_left _ _
  have hsd : ∀ n k, s n k+d n k=e n k := fun n k => add_tsub_cancel_of_le (hse n k)
  have hdpos : ∀ n k, d n k ≠ 0 → s n k < e n k := by
    intro n k hk
    exact (tsub_pos_iff_lt).mp (pos_iff_ne_zero.mpr hk)
  let a : (n : ℕ) → κ n → ℝ≥0 := fun n k =>
    if d n k = 0 then 0 else itoUniformNNTime T (n+1) k.1
  let b : (n : ℕ) → κ n → ℝ≥0 := fun n k =>
    if d n k = 0 then 0 else itoUniformNNTime t (n+1) k.2
  have hpast : ∀ n k, a n k ≤ s n k ∧ b n k ≤ s n k := by
    intro n k
    by_cases hz : d n k = 0
    · simp [a, b, hz]
    · have hh := itoHorizonIntersection_positive_samples T t (n+1) (n+1) k.1 k.2 (hdpos n k hz)
      simpa only [a, b, ite_eq_right hz] using ⟨hh.1, hh.2.1⟩
  have has : ∀ n k, a n k ∈ Set.Icc 0 T := by
    intro n k
    by_cases hz : d n k = 0
    · simp [a, hz]
    · have hh := itoHorizonIntersection_positive_samples T t (n+1) (n+1) k.1 k.2 (hdpos n k hz)
      exact ⟨bot_le, by simpa only [a, ite_eq_right hz] using hh.2.2.le.trans ht⟩
  have hbs : ∀ n k, b n k ∈ Set.Icc 0 T := by
    intro n k
    by_cases hz : d n k = 0
    · simp [b, hz]
    · exact ⟨bot_le, by simpa only [b, ite_eq_right hz] using
        (itoUniformNNTime_le_end t (n+1) k.2 (Nat.succ_pos n) k.2.is_lt.le).trans ht⟩
  have hdisj : ∀ n i k, i ≠ k → d n i ≠ 0 → d n k ≠ 0 →
      s n i+d n i ≤ s n k ∨ s n k+d n k ≤ s n i := by
    intro n i k hik hdi hdk
    have hn : (i.1.val, i.2.val) ≠ (k.1.val, k.2.val) := by
      intro hh
      apply hik
      apply Prod.ext <;> apply Fin.ext
      · exact congrArg Prod.fst hh
      · exact congrArg Prod.snd hh
    have hh := itoHorizonIntersections_disjoint T t (n+1) (n+1) i.1 i.2 k.1 k.2 hn
    have hl : min (e n i) (e n k) ≤ max (s n i) (s n k) := Set.Ioc_disjoint_Ioc.mp hh
    rw [hsd, hsd]
    rcases le_total (s n i) (s n k) with h | h
    · rw [max_eq_right h] at hl
      exact Or.inl ((min_le_iff.mp hl).resolve_right (not_le.mpr (hdpos n k hdk)))
    · rw [max_eq_left h] at hl
      exact Or.inr ((min_le_iff.mp hl).resolve_left (not_le.mpr (hdpos n i hdi)))
  have hdtotal : ∀ n, ∑ k, (d n k : ℝ) ≤ T := by
    intro n
    have hh := itoHorizonIntersections_total_duration T t ht (n+1) (n+1)
      (Nat.succ_pos n) (Nat.succ_pos n)
    simp only [←Fin.sum_univ_eq_sum_range] at hh
    have hsum : (∑ k : κ n, d n k) = t := by
      simpa only [κ, Fintype.sum_prod_type, d, e, s] using hh
    have hr := congrArg (fun x : ℝ≥0 => (x : ℝ)) hsum
    simp only [NNReal.coe_sum] at hr
    exact hr.le.trans ht
  let δ : ℕ → ℝ := fun n => (T : ℝ)/(n+1)+(t : ℝ)/(n+1)
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa [δ, div_eq_mul_inv, mul_assoc] using (h0.const_mul (T : ℝ)).add (h0.const_mul (t : ℝ))
  have hdist : ∀ n k, dist (a n k) (b n k) ≤ δ n := by
    intro n k
    by_cases hz : d n k = 0
    · simp only [a, b, ite_eq_left hz, dist_self]
      dsimp [δ]
      positivity
    · simpa only [a, b, ite_eq_right hz, δ, Nat.cast_add, Nat.cast_one] using
        itoHorizonIntersection_sample_dist_le T t (n+1) (n+1) k.1 k.2
          (Nat.succ_pos n) (Nat.succ_pos n) (hdpos n k hz)
  have hlim := brownianDisjointSampleDifferences_tendsto_meanSquare B P hB hind j κ
    s d a b hdisj (fun n k => (hpast n k).1) (fun n k => (hpast n k).2)
    T has hbs hdtotal F hF hFi δ hδ hdist hc C hC hbound
  convert hlim using 1
  ext n
  apply integral_congr_ae
  apply ae_of_all
  intro ω
  dsimp only
  apply congrArg (fun r : ℝ => r^2)
  rw [brownianUniformPartialSum_difference_horizon_refinement (B j) F F T t ht
    (n+1) (n+1) (Nat.succ_pos n) (Nat.succ_pos n) ω]
  simp only [←Fin.sum_univ_eq_sum_range]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hz : d n (i, k) = 0
  · have heq : e n (i, k) = s n (i, k) := by
      have hh := hsd n (i, k)
      simpa [hz] using hh.symm
    change (F (itoUniformNNTime T (n+1) i) ω-F (itoUniformNNTime t (n+1) k) ω)*
      (B j (e n (i, k)) ω-B j (s n (i, k)) ω) = _
    rw [heq]
    simp [a, b, hz]
  · change (F (itoUniformNNTime T (n+1) i) ω-F (itoUniformNNTime t (n+1) k) ω)*
      (B j (e n (i, k)) ω-B j (s n (i, k)) ω) = _
    simp only [a, b, ite_eq_right hz, hsd]

end
end GinibrePoincare
