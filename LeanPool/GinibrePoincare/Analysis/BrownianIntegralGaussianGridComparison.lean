/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralGaussianGridComparison.lean.
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
# Brownian integral Gaussian grid comparison

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianActualLeftGridSum_difference_tendsto_meanSquare`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

/-- The left-endpoint Itô sum `∑ k < N, F (a k) ω * (B (a (k + 1)) ω - B (a k) ω)` of the
integrand `F` against `B` along the time grid `a`. -/
def brownianActualLeftGridSum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (F : ℝ≥0 → Ω → ℝ) (a : ℕ → ℝ≥0) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range N, F (a k) ω*(B (a (k+1)) ω-B (a k) ω)

/-- Actual Brownian left sums on two arbitrary vanishing-mesh endpoint grids
have the same mean-square limit. All innovation laws and isometry estimates
are derived from the original Brownian family. -/
theorem brownianActualLeftGridSum_difference_tendsto_meanSquare
    {Ω ι : Type*} [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F t))
    (hFi : ∀ t, MemLp (F t) 2 P) (H : ℝ≥0)
    (a c : ℕ → ℕ → ℝ≥0) (N M : ℕ → ℕ) (hN : ∀ n, 0 < N n) (hM : ∀ n, 0 < M n)
    (ha : ∀ n, Monotone (a n)) (hc : ∀ n, Monotone (c n))
    (ha0 : ∀ n, a n 0 = 0) (hc0 : ∀ n, c n 0 = 0)
    (haN : ∀ n, a n (N n) = H) (hcM : ∀ n, c n (M n) = H)
    (ma mc : ℕ → ℝ) (hma : Tendsto ma atTop (𝓝 0)) (hmc : Tendsto mc atTop (𝓝 0))
    (hmap : ∀ n, 0 ≤ ma n) (hmcp : ∀ n, 0 ≤ mc n)
    (hstepA : ∀ n k, k < N n → (a n (k + 1) : ℝ) - a n k ≤ ma n)
    (hstepC : ∀ n k, k < M n → (c n (k + 1) : ℝ) - c n k ≤ mc n)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => F t ω) (Set.Icc 0 H))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ t ω, ‖F t ω‖ ≤ C) :
    Tendsto (fun n => ∫ ω,
      (brownianActualLeftGridSum (B j) F (a n) (N n) ω-
        brownianActualLeftGridSum (B j) F (c n) (M n) ω)^2 ∂P) atTop (𝓝 0) := by
  have := Fintype.ofFinite ι
  classical
  let κ := fun n => Fin (N n) × Fin (M n)
  let : ∀ n, Nonempty (κ n) := fun n => ⟨(⟨0, hN n⟩, ⟨0, hM n⟩)⟩
  let s : (n : ℕ) → κ n → ℝ≥0 := fun n k => max (a n k.1) (c n k.2)
  let e : (n : ℕ) → κ n → ℝ≥0 := fun n k => max (s n k)
    (min (a n (k.1.val+1)) (c n (k.2.val+1)))
  let d : (n : ℕ) → κ n → ℝ≥0 := fun n k => e n k-s n k
  have hse : ∀ n k, s n k ≤ e n k := fun n k => le_max_left _ _
  have hsd : ∀ n k, s n k+d n k=e n k := fun n k => add_tsub_cancel_of_le (hse n k)
  have hdpos : ∀ n k, d n k ≠ 0 → s n k < e n k := by
    intro n k hk
    exact tsub_pos_iff_lt.mp (pos_iff_ne_zero.mpr hk)
  let A : (n : ℕ) → κ n → ℝ≥0 := fun n k => if d n k=0 then 0 else a n k.1
  let D : (n : ℕ) → κ n → ℝ≥0 := fun n k => if d n k=0 then 0 else c n k.2
  have hpast : ∀ n k, A n k ≤ s n k ∧ D n k ≤ s n k := by
    intro n k
    by_cases hz : d n k=0
    · simp [A, D, hz]
    · exact ⟨by simpa only [A, ite_eq_right hz, s] using (le_max_left (a n k.1) (c n k.2)),
        by simpa only [D, ite_eq_right hz, s] using (le_max_right (a n k.1) (c n k.2))⟩
  have hAs : ∀ n k, A n k ∈ Set.Icc 0 H := by
    intro n k
    by_cases hz : d n k=0
    · simp [A, hz]
    · refine ⟨bot_le,?_⟩
      simpa only [A, ite_eq_right hz, haN n] using ha n k.1.is_lt.le
  have hDs : ∀ n k, D n k ∈ Set.Icc 0 H := by
    intro n k
    by_cases hz : d n k=0
    · simp [D, hz]
    · refine ⟨bot_le,?_⟩
      simpa only [D, ite_eq_right hz, hcM n] using hc n k.2.is_lt.le
  have hdisj : ∀ n i k, i≠k → d n i≠0 → d n k≠0 →
      s n i+d n i ≤ s n k ∨ s n k+d n k ≤ s n i := by
    intro n i k hik hdi hdk
    have hn : (i.1.val, i.2.val) ≠ (k.1.val, k.2.val) := by
      intro hh
      apply hik
      apply Prod.ext <;> apply Fin.ext
      · exact congrArg Prod.fst hh
      · exact congrArg Prod.snd hh
    have hh := itoGridIntersections_disjoint (a n) (c n) (ha n) (hc n) i.1 i.2 k.1 k.2 hn
    have hl : min (e n i) (e n k) ≤ max (s n i) (s n k) := Set.Ioc_disjoint_Ioc.mp hh
    rw [hsd, hsd]
    rcases le_total (s n i) (s n k) with h | h
    · rw [max_eq_right h] at hl
      exact Or.inl ((min_le_iff.mp hl).resolve_right (not_le.mpr (hdpos n k hdk)))
    · rw [max_eq_left h] at hl
      exact Or.inr ((min_le_iff.mp hl).resolve_left (not_le.mpr (hdpos n i hdi)))
  have hdtotal : ∀ n, ∑ k, (d n k : ℝ) ≤ H := by
    intro n
    have hh := itoGridIntersections_total_duration H (a n) (c n) (N n) (M n)
      (ha n) (hc n) (ha0 n) (haN n) (hc0 n) (hcM n)
    simp only [←Fin.sum_univ_eq_sum_range] at hh
    change (∑ k : Fin (N n) × Fin (M n), ((e n k-s n k : ℝ≥0) : ℝ)) ≤ H
    simp only [Fintype.sum_prod_type]
    simp_rw [NNReal.coe_sub (hse n _)]
    exact hh.le
  have hdist : ∀ n k, dist (A n k) (D n k) ≤ ma n+mc n := by
    intro n k
    by_cases hz : d n k=0
    · simpa [A, D, hz] using add_nonneg (hmap n) (hmcp n)
    · have he := itoIntersection_end_eq_of_positive _ _ _ _ (hdpos n k hz)
      have hcb : c n k.2 ≤ a n (k.1.val+1) :=
        (le_max_right _ _).trans ((hdpos n k hz).le.trans (he.le.trans (min_le_left _ _)))
      have had : a n k.1 ≤ c n (k.2.val+1) :=
        (le_max_left _ _).trans ((hdpos n k hz).le.trans (he.le.trans (min_le_right _ _)))
      have hcbR : (c n k.2 : ℝ) ≤ a n (k.1.val+1) := hcb
      have hadR : (a n k.1 : ℝ) ≤ c n (k.2.val+1) := had
      have hAstep := hstepA n k.1 k.1.is_lt
      have hCstep := hstepC n k.2 k.2.is_lt
      simp only [A, D, ite_eq_right hz, NNReal.dist_eq]
      rcases le_total (a n k.1 : ℝ) (c n k.2 : ℝ) with h | h
      · rw [abs_of_nonpos (sub_nonpos.mpr h)]
        have := hmcp n
        linarith
      · rw [abs_of_nonneg (sub_nonneg.mpr h)]
        have := hmap n
        linarith
  have hlim := brownianDisjointSampleDifferences_tendsto_meanSquare B P hB hind j κ s d A D
    hdisj (fun n k => (hpast n k).1) (fun n k => (hpast n k).2) H hAs hDs hdtotal
    F hF hFi (fun n => ma n+mc n) (by simpa using hma.add hmc) hdist hcont C hC hbound
  convert hlim using 1
  ext n
  apply integral_congr_ae
  apply ae_of_all
  intro ω
  dsimp only
  apply congrArg (fun r : ℝ => r^2)
  unfold brownianActualLeftGridSum
  rw [itoWeightedIntervalSums_difference_intersections (fun t => B j t ω) H (a n) (c n)
    (N n) (M n) (ha n) (hc n) (ha0 n) (haN n) (hc0 n) (hcM n)
    (fun i => F (a n i) ω) (fun j => F (c n j) ω)]
  simp only [←Fin.sum_univ_eq_sum_range]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hz : d n (i, k)=0
  · have heq : e n (i, k)=s n (i, k) := by simpa [hz] using (hsd n (i, k)).symm
    change (F (a n i) ω-F (c n k) ω)*(B j (e n (i, k)) ω-B j (s n (i, k)) ω) = _
    rw [heq]
    simp [A, D, hz]
  · change (F (a n i) ω-F (c n k) ω)*(B j (e n (i, k)) ω-B j (s n (i, k)) ω) = _
    simp only [A, D, ite_eq_right hz, hsd]

end
end GinibrePoincare
