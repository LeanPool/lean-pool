/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/FiniteDimensionalItoIntervalRefinementGeometry.lean.
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

public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoIntervalRefinementBrownian

/-!
# Finite dimensional Ito interval refinement geometry

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `itoHorizonIntersection_sample_dist_le`, `itoHorizonIntersections_disjoint`,
`itoHorizonIntersections_total_duration`.
-/

@[expose] public section

open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- A positive intersection has its true minimum endpoint. -/
theorem itoIntersection_end_eq_of_positive (a b c d : ℝ≥0)
    (h : max a c < max (max a c) (min b d)) :
    max (max a c) (min b d) = min b d := by
  have hh : max a c < min b d := (lt_max_iff.mp h).resolve_left (lt_irrefl _)
  exact max_eq_right hh.le

/-- Any point in a literal intersection interval lies inside both original
half-open intervals. -/
theorem itoIntersection_mem_bounds (a b c d x : ℝ≥0)
    (hx : x ∈ Set.Ioc (max a c) (max (max a c) (min b d))) :
    a < x ∧ x ≤ b ∧ c < x ∧ x ≤ d := by
  have he := itoIntersection_end_eq_of_positive a b c d (hx.1.trans_le hx.2)
  rw [he] at hx
  exact ⟨(le_max_left _ _).trans_lt hx.1, hx.2.trans (min_le_left _ _),
    (le_max_right _ _).trans_lt hx.1, hx.2.trans (min_le_right _ _)⟩

/-- Distinct cells of two monotone grids have disjoint literal intersection
intervals, including every empty cell. -/
theorem itoGridIntersections_disjoint (a c : ℕ → ℝ≥0) (ha : Monotone a) (hc : Monotone c)
    (i j k l : ℕ) (hne : (i, j) ≠ (k, l)) :
    Disjoint (Set.Ioc (max (a i) (c j)) (max (max (a i) (c j)) (min (a (i+1)) (c (j+1)))))
      (Set.Ioc (max (a k) (c l)) (max (max (a k) (c l)) (min (a (k+1)) (c (l+1))))) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨hax, hxa, hcx, hxc⟩ := itoIntersection_mem_bounds _ _ _ _ _ hx
  obtain ⟨hak, hxk, hcl, hxl⟩ := itoIntersection_mem_bounds _ _ _ _ _ hy
  have hik : i = k := by
    by_contra h
    rcases lt_or_gt_of_ne h with h | h
    · exact (not_lt_of_ge (hxa.trans (ha (Nat.succ_le_of_lt h)))) hak
    · exact (not_lt_of_ge (hxk.trans (ha (Nat.succ_le_of_lt h)))) hax
  have hjl : j = l := by
    by_contra h
    rcases lt_or_gt_of_ne h with h | h
    · exact (not_lt_of_ge (hxc.trans (hc (Nat.succ_le_of_lt h)))) hcl
    · exact (not_lt_of_ge (hxl.trans (hc (Nat.succ_le_of_lt h)))) hcx
  exact hne (by simp [hik, hjl])

/-- The total real duration of the literal intersection refinement is the
original horizon, even for nonuniform and noncommensurate grids. -/
theorem itoGridIntersections_total_duration
    (T : ℝ≥0) (a c : ℕ → ℝ≥0) (N M : ℕ)
    (ha : Monotone a) (hc : Monotone c)
    (ha0 : a 0 = 0) (haN : a N = T) (hc0 : c 0 = 0) (hcM : c M = T) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M,
      (((max (max (a i) (c j)) (min (a (i+1)) (c (j+1))) : ℝ≥0) : ℝ) -
        ((max (a i) (c j) : ℝ≥0) : ℝ))) = T := by
  have hh := itoWeightedIntervalSums_difference_intersections (fun s => (s : ℝ)) T a c N M
    ha hc ha0 haN hc0 hcM (fun _ => 1) (fun _ => 0)
  simp only [one_mul, zero_mul, Finset.sum_const_zero, sub_zero] at hh
  rw [Finset.sum_range_sub (fun i => (a i : ℝ)) N, haN, ha0] at hh
  simpa only [NNReal.coe_zero, sub_zero] using hh.symm

/-- Actual intersection grid for the fixed-T partial sum and horizon-t sum. -/
def itoHorizonIntersectionStart (T t : ℝ≥0) (N M i j : ℕ) : ℝ≥0 :=
  max (min t (itoUniformNNTime T N i)) (itoUniformNNTime t M j)
/-- The right endpoint of the intersection of the `i`-th cell of the uniform `N`-step partition
of `[0, T]` (truncated at `t`) with the `j`-th cell of the uniform `M`-step partition of `[0, t]`,
clamped below by the left endpoint `itoHorizonIntersectionStart T t N M i j`. -/
def itoHorizonIntersectionEnd (T t : ℝ≥0) (N M i j : ℕ) : ℝ≥0 :=
  max (itoHorizonIntersectionStart T t N M i j)
    (min (min t (itoUniformNNTime T N (i+1))) (itoUniformNNTime t M (j+1)))

/-- Positivity of an actual overlap forces both original sampled coefficients
into the true past of its start. -/
theorem itoHorizonIntersection_positive_samples
    (T t : ℝ≥0) (N M i j : ℕ)
    (h : itoHorizonIntersectionStart T t N M i j < itoHorizonIntersectionEnd T t N M i j) :
    itoUniformNNTime T N i ≤ itoHorizonIntersectionStart T t N M i j ∧
      itoUniformNNTime t M j ≤ itoHorizonIntersectionStart T t N M i j ∧
      itoUniformNNTime T N i < t := by
  have he := itoIntersection_end_eq_of_positive _ _ _ _ h
  have hstart : itoHorizonIntersectionStart T t N M i j < t := by
    exact h.trans_le (he.le.trans ((min_le_left _ _).trans (min_le_left _ _)))
  have ha : itoUniformNNTime T N i < t := by
    by_contra hh
    have htai := le_of_not_gt hh
    have hh : t ≤ itoHorizonIntersectionStart T t N M i j := by
      simp [itoHorizonIntersectionStart, min_eq_left htai]
    exact (not_lt_of_ge hh) hstart
  exact ⟨by simp [itoHorizonIntersectionStart, min_eq_right ha.le], le_max_right _ _, ha⟩

/-- Samples whose cells actually overlap are at distance at most the sum of
the two true time meshes. -/
theorem itoHorizonIntersection_sample_dist_le
    (T t : ℝ≥0) (N M i j : ℕ) (hN : 0 < N) (hM : 0 < M)
    (h : itoHorizonIntersectionStart T t N M i j < itoHorizonIntersectionEnd T t N M i j) :
    dist (itoUniformNNTime T N i) (itoUniformNNTime t M j) ≤
      (T : ℝ)/N + (t : ℝ)/M := by
  obtain ⟨ha, hc, hat⟩ := itoHorizonIntersection_positive_samples T t N M i j h
  have he := itoIntersection_end_eq_of_positive _ _ _ _ h
  have hcb : itoUniformNNTime t M j ≤ itoUniformNNTime T N (i+1) :=
    hc.trans (h.le.trans (he.le.trans ((min_le_left _ _).trans (min_le_right _ _))))
  have had : itoUniformNNTime T N i ≤ itoUniformNNTime t M (j+1) :=
    ha.trans (h.le.trans (he.le.trans (min_le_right _ _)))
  have hstepA := itoUniformNNTime_increment_coe T N i
  have hstepC := itoUniformNNTime_increment_coe t M j
  have hcbR : (itoUniformNNTime t M j : ℝ) ≤ itoUniformNNTime T N (i+1) := hcb
  have hadR : (itoUniformNNTime T N i : ℝ) ≤ itoUniformNNTime t M (j+1) := had
  rw [NNReal.dist_eq]
  rcases le_total (itoUniformNNTime T N i : ℝ) (itoUniformNNTime t M j : ℝ) with hac | hca
  · rw [abs_of_nonpos (sub_nonpos.mpr hac)]
    have hpos : 0 ≤ (t : ℝ)/M := by positivity
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hca)]
    have hpos : 0 ≤ (T : ℝ)/N := by positivity
    linarith

/-- Actual clipped-horizon intersection cells are pairwise disjoint. -/
theorem itoHorizonIntersections_disjoint (T t : ℝ≥0) (N M i j k l : ℕ)
    (hne : (i, j) ≠ (k, l)) :
    Disjoint (Set.Ioc (itoHorizonIntersectionStart T t N M i j)
      (itoHorizonIntersectionEnd T t N M i j))
      (Set.Ioc (itoHorizonIntersectionStart T t N M k l)
        (itoHorizonIntersectionEnd T t N M k l)) :=
  itoGridIntersections_disjoint (fun i => min t (itoUniformNNTime T N i))
    (itoUniformNNTime t M) (monotone_const.min (itoUniformNNTime_mono T N))
    (itoUniformNNTime_mono t M) i j k l hne

/-- The actual nonnegative durations of every cell sum exactly to t. -/
theorem itoHorizonIntersections_total_duration (T t : ℝ≥0) (ht : t ≤ T)
    (N M : ℕ) (hN : 0 < N) (hM : 0 < M) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M,
      (itoHorizonIntersectionEnd T t N M i j-itoHorizonIntersectionStart T t N M i j)) = t := by
  apply NNReal.coe_injective
  simp only [NNReal.coe_sum]
  simp only [itoHorizonIntersectionEnd, itoHorizonIntersectionStart]
  simp_rw [NNReal.coe_sub (le_max_left _ _)]
  exact itoGridIntersections_total_duration t
    (fun i => min t (itoUniformNNTime T N i)) (itoUniformNNTime t M) N M
    (monotone_const.min (itoUniformNNTime_mono T N)) (itoUniformNNTime_mono t M)
    (by simp [itoUniformNNTime, itoUniformTime])
    (by rw [itoUniformNNTime_end T N hN, min_eq_left ht])
    (by simp [itoUniformNNTime, itoUniformTime]) (itoUniformNNTime_end t M hM)

end
end GinibrePoincare
