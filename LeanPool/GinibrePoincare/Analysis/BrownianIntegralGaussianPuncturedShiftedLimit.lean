/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralGaussianPuncturedShiftedLimit.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGaussianPuncturedConcatenatedComparison
public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGaussianShiftedLimit

/-!
# Brownian integral Gaussian punctured shifted limit

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `brownianUnitShiftedUniformSum_punctured_tendstoInMeasure_of_horizon_limits`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

/-- Ordinary horizon limits determine the actual shifted interval integral;
no shifted limit, Gaussian law, or independence is assumed. -/
theorem brownianUnitShiftedUniformSum_punctured_tendstoInMeasure_of_horizon_limits
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (u : ℝ≥0 → Ω → EuclideanSpace ℝ ι)
    (hu : ∀ r, @Measurable Ω (EuclideanSpace ℝ ι)
      (ginibreBrownianAugmentedFiltration B P hB r) _ (u r))
    (hui : ∀ r i, MemLp (fun ω => u r ω i) 2 P)
    (huc : ∀ᵐ ω ∂P, ContinuousOn (fun r => u r ω) (Set.Ioi 0))
    (C : ℝ) (hC : 0 ≤ C) (hub : ∀ r ω i, ‖u r ω i‖ ≤ C)
    (s t : ℝ≥0) (I J : Ω → ℝ)
    (hI : TendstoInMeasure P (fun n ω => ∑ i, brownianUniformLeftSum (B i)
      (fun r ω => u r ω i) (s + t) (n + 1) ω) atTop I)
    (hJ : TendstoInMeasure P (fun n ω => ∑ i, brownianUniformLeftSum (B i)
      (fun r ω => u r ω i) s (n + 1) ω) atTop J) :
    TendstoInMeasure P (fun n => brownianUnitShiftedUniformSum B u s t (n+1))
      atTop (fun ω => I ω-J ω) := by
  classical
  classical
  let A : ℕ → Ω → ℝ := fun n ω => ∑ i, brownianUniformLeftSum (B i)
    (fun r ω => u r ω i) (s+t) (n+1) ω
  let D : ℕ → Ω → ℝ := fun n ω => ∑ i, brownianActualLeftGridSum (B i)
    (fun r ω => u r ω i) (itoConcatenatedGrid s t (n+1)) ((n+1)+(n+1)) ω
  let R : ℕ → Ω → ℝ := fun n ω => ∑ i, brownianUniformLeftSum (B i)
    (fun r ω => u r ω i) s (n+1) ω
  have hum (r : ℝ≥0) (i : ι) : @Measurable Ω ℝ
      (ginibreBrownianAugmentedFiltration B P hB r) _ (fun ω => u r ω i) :=
    (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i).measurable.comp (hu r)
  have huc' (i : ι) : ∀ᵐ ω ∂P, ContinuousOn (fun r => u r ω i) (Set.Ioi 0) := by
    filter_upwards [huc] with ω hω
    exact (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i).comp_continuousOn hω
  have hAm (n : ℕ) : MemLp (A n) 2 P := by
    apply memLp_finsetSum
    intro i hi
    exact brownianActualLeftGridSum_memLp_two B P hB hind i _ (fun r => hum r i)
      (fun r => hui r i) _ (itoUniformNNTime_mono _ _) _
  have hDm (n : ℕ) : MemLp (D n) 2 P := by
    apply memLp_finsetSum
    intro i hi
    exact brownianActualLeftGridSum_memLp_two B P hB hind i _ (fun r => hum r i)
      (fun r => hui r i) _ (itoConcatenatedGrid_monotone _ _ _ (Nat.succ_pos n)) _
  have hRm (n : ℕ) : MemLp (R n) 2 P := by
    apply memLp_finsetSum
    intro i hi
    exact brownianActualLeftGridSum_memLp_two B P hB hind i _ (fun r => hum r i)
      (fun r => hui r i) _ (itoUniformNNTime_mono _ _) _
  have herr : TendstoInMeasure P (fun n ω => A n ω-D n ω) atTop (fun _ => 0) := by
    have hi (i : ι) := brownianUniformLeftSum_concatenated_punctured_difference_tendsto_meanSquare
      B P hB hind i (fun r ω => u r ω i) (fun r => hum r i) (fun r => hui r i)
      s t (huc' i) C hC (fun r ω => hub r ω i)
    have hcoord (i : ι) : TendstoInMeasure P (fun n ω =>
        brownianUniformLeftSum (B i) (fun r ω => u r ω i) (s+t) (n+1) ω-
        brownianActualLeftGridSum (B i) (fun r ω => u r ω i)
          (itoConcatenatedGrid s t (n+1)) ((n+1)+(n+1)) ω) atTop (fun _ => 0) := by
      apply ginibre_tendstoInMeasure_of_meanSquare P _ _
      · intro n
        have ha := brownianActualLeftGridSum_memLp_two B P hB hind i _
          (fun r => hum r i) (fun r => hui r i) (itoUniformNNTime (s+t) (n+1))
              (itoUniformNNTime_mono (s+t) (n+1)) (n+1)
        have hd := brownianActualLeftGridSum_memLp_two B P hB hind i _
          (fun r => hum r i) (fun r => hui r i) (itoConcatenatedGrid s t (n+1))
          (itoConcatenatedGrid_monotone s t (n+1) (Nat.succ_pos n)) ((n+1)+(n+1))
        simpa only [sub_zero, brownianActualLeftGridSum, brownianUniformLeftSum, Pi.sub_apply] using
            (ha.sub hd).integrable_sq
      · simpa only [sub_zero] using hi i
    have hsum := itoTendstoInMeasure_finset_sum P Finset.univ _ _
      (fun i n => by
        have ha := brownianActualLeftGridSum_memLp_two B P hB hind i _
          (fun r => hum r i) (fun r => hui r i) (itoUniformNNTime (s+t) (n+1))
              (itoUniformNNTime_mono (s+t) (n+1)) (n+1)
        have hd := brownianActualLeftGridSum_memLp_two B P hB hind i _
          (fun r => hum r i) (fun r => hui r i) (itoConcatenatedGrid s t (n+1))
          (itoConcatenatedGrid_monotone s t (n+1) (Nat.succ_pos n)) ((n+1)+(n+1))
        exact (ha.sub hd).aestronglyMeasurable) (fun i => hcoord i)
    simpa only [A, D, Finset.sum_sub_distrib, Finset.sum_const_zero] using hsum
  have hDl := actualTendstoInMeasure_sub P A (fun n ω => A n ω-D n ω) I (fun _ => 0)
    (fun n => (hAm n).aestronglyMeasurable)
    (fun n => ((hAm n).sub (hDm n)).aestronglyMeasurable) hI herr
  have hDl' : TendstoInMeasure P D atTop I := by
    simpa only [sub_sub_cancel, sub_zero] using hDl
  have h := actualTendstoInMeasure_sub P D R I J
    (fun n => (hDm n).aestronglyMeasurable) (fun n => (hRm n).aestronglyMeasurable) hDl' hJ
  have he : (fun n ω => D n ω-R n ω) =
      (fun n => brownianUnitShiftedUniformSum B u s t (n+1)) := by
    funext n ω
    simp only [D, R, brownianUnitShiftedUniformSum]
    simp_rw [brownianActualLeftGridSum_concatenated _ _ s t (n+1) (Nat.succ_pos n) ω]
    rw [Finset.sum_add_distrib]
    ring
  rw [he] at h
  exact h

end
end GinibrePoincare
