/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/FiniteDimensionalItoIntervalRefinement.lean.
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

public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoUniformRefinement

/-!
# Finite dimensional Ito interval refinement

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `itoWeightedIntervalSums_difference_intersections`.
-/

@[expose] public section

open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- Clamp a time to an actual ordered interval. -/
def itoIntervalClamp (a b x : ℝ≥0) : ℝ≥0 := max a (min b x)

/-- The clamped Brownian increment is symmetric under exchanging the two
actual intervals, including the empty-intersection case. -/
theorem itoIntervalClamp_increment_comm {E : Type*} [AddCommGroup E]
    (B : ℝ≥0 → E) (a b c d : ℝ≥0) (hab : a ≤ b) (hcd : c ≤ d) :
    B (itoIntervalClamp a b d)-B (itoIntervalClamp a b c) =
      B (itoIntervalClamp c d b)-B (itoIntervalClamp c d a) := by
  have aux : ∀ a b c d : ℝ≥0, a ≤ b → c ≤ d → a ≤ c →
      B (itoIntervalClamp a b d)-B (itoIntervalClamp a b c) =
      B (itoIntervalClamp c d b)-B (itoIntervalClamp c d a) := by
    intro a b c d hab hcd hac
    by_cases hbc : b ≤ c
    · have hbd := hbc.trans hcd
      have had := hac.trans hcd
      simp [itoIntervalClamp, min_eq_left hbd, min_eq_left hbc,
        min_eq_right had, min_eq_right hbd, max_eq_right hab, max_eq_left hac, max_eq_left hbc]
    · have hcb : c ≤ b := le_of_not_ge hbc
      have had := hac.trans hcd
      by_cases hdb : d ≤ b
      · simp [itoIntervalClamp, min_eq_right hdb, min_eq_right hcb,
          min_eq_right had, min_eq_left hdb, max_eq_right hac, max_eq_right had,
          max_eq_right hcd, max_eq_left hac]
      · have hbd : b ≤ d := le_of_not_ge hdb
        simp [itoIntervalClamp, min_eq_left hbd, min_eq_right hcb,
          min_eq_right had, min_eq_right hbd, max_eq_right hab, max_eq_right hac,
          max_eq_left hac, max_eq_right hcb]
  rcases le_total a c with hac | hca
  · exact aux a b c d hab hcd hac
  · exact (aux c d a b hcd hab hca).symm

/-- Actual refinement increments telescope across any second endpoint grid. -/
theorem itoIntervalClamp_increment_sum {E : Type*} [AddCommGroup E]
    (B : ℝ≥0 → E) (a b T : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (c : ℕ → ℝ≥0) (N : ℕ) (hc0 : c 0 = 0) (hcN : c N = T) :
    (∑ j ∈ Finset.range N,
      (B (itoIntervalClamp a b (c (j+1)))-B (itoIntervalClamp a b (c j)))) = B b-B a := by
  rw [Finset.sum_range_sub (fun j => B (itoIntervalClamp a b (c j))) N]
  simp [hcN, hc0, itoIntervalClamp, min_eq_left hbT, max_eq_right hab]

/-- Difference of two actual weighted left sums equals the double sum over
intersection increments. Grids may be noncommensurate and nonuniform. -/
theorem itoWeightedIntervalSums_difference_refinement
    (B : ℝ≥0 → ℝ) (T : ℝ≥0) (a c : ℕ → ℝ≥0) (N M : ℕ)
    (ha : Monotone a) (hc : Monotone c)
    (ha0 : a 0 = 0) (haN : a N = T) (hc0 : c 0 = 0) (hcM : c M = T)
    (F G : ℕ → ℝ) :
    (∑ i ∈ Finset.range N, F i*(B (a (i+1))-B (a i))) -
      (∑ j ∈ Finset.range M, G j*(B (c (j+1))-B (c j))) =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M,
        (F i-G j)*(B (itoIntervalClamp (a i) (a (i+1)) (c (j+1)))-
          B (itoIntervalClamp (a i) (a (i+1)) (c j))) := by
  have hleft : (∑ i ∈ Finset.range N, F i*(B (a (i+1))-B (a i))) =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M,
        F i*(B (itoIntervalClamp (a i) (a (i+1)) (c (j+1)))-
          B (itoIntervalClamp (a i) (a (i+1)) (c j))) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [←Finset.mul_sum, itoIntervalClamp_increment_sum B (a i) (a (i+1)) T
      (ha (Nat.le_succ i)) (by rw [←haN];exact ha (Nat.succ_le_of_lt (Finset.mem_range.mp hi)))
      c M hc0 hcM]
  have hright : (∑ j ∈ Finset.range M, G j*(B (c (j+1))-B (c j))) =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M,
        G j*(B (itoIntervalClamp (a i) (a (i+1)) (c (j+1)))-
          B (itoIntervalClamp (a i) (a (i+1)) (c j))) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    simp_rw [itoIntervalClamp_increment_comm B _ _ _ _ (ha (Nat.le_succ _)) (hc (Nat.le_succ _))]
    rw [←Finset.mul_sum, itoIntervalClamp_increment_sum B (c j) (c (j+1)) T
      (hc (Nat.le_succ j)) (by rw [←hcM];exact hc (Nat.succ_le_of_lt (Finset.mem_range.mp hj)))
      a N ha0 haN]
  rw [hleft, hright,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The symmetric clamped increment is exactly the actual intersection
increment, with its endpoint set equal to its start when the intersection is empty. -/
theorem itoIntervalClamp_increment_eq_intersection {E : Type*} [AddCommGroup E]
    (B : ℝ≥0 → E) (a b c d : ℝ≥0) (hab : a ≤ b) (hcd : c ≤ d) :
    B (itoIntervalClamp a b d)-B (itoIntervalClamp a b c) =
      B (max (max a c) (min b d))-B (max a c) := by
  by_cases hbc : b ≤ c
  · have hbd := hbc.trans hcd
    have hac := hab.trans hbc
    have hm : min b d ≤ c := (min_le_left _ _).trans hbc
    simp [itoIntervalClamp, min_eq_left hbc, min_eq_left hbd, max_eq_right hab,
      max_eq_right hac, max_eq_left hbc]
  · have hcb : c ≤ b := le_of_not_ge hbc
    have hm : c ≤ min b d := le_min hcb hcd
    simp only [itoIntervalClamp, min_eq_right hcb]
    rw [max_assoc, max_eq_right hm]

/-- Exact refinement using literal nonnegative intersection endpoints. -/
theorem itoWeightedIntervalSums_difference_intersections
    (B : ℝ≥0 → ℝ) (T : ℝ≥0) (a c : ℕ → ℝ≥0) (N M : ℕ)
    (ha : Monotone a) (hc : Monotone c)
    (ha0 : a 0 = 0) (haN : a N = T) (hc0 : c 0 = 0) (hcM : c M = T)
    (F G : ℕ → ℝ) :
    (∑ i ∈ Finset.range N, F i*(B (a (i+1))-B (a i))) -
      (∑ j ∈ Finset.range M, G j*(B (c (j+1))-B (c j))) =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M,
        (F i-G j)*(B (max (max (a i) (c j)) (min (a (i+1)) (c (j+1))))-
          B (max (a i) (c j))) := by
  rw [itoWeightedIntervalSums_difference_refinement B T a c N M ha hc ha0 haN hc0 hcM]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [itoIntervalClamp_increment_eq_intersection B _ _ _ _
    (ha (Nat.le_succ i)) (hc (Nat.le_succ j))]

end
end GinibrePoincare
