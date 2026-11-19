/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralUniformSums.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralIsometry
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralCoefficientMesh
public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoUniformRefinement

/-! Genuine common-refinement second moments for Brownian left sums. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

/-- The left-point sum `∑ F tᵢ (B tᵢ₊₁ - B tᵢ)` of `F` against `B` over the uniform partition of
`[0, T]` into `N` steps. -/
def brownianUniformLeftSum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (F : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range N, F (itoUniformNNTime T N i) ω*
    (B (itoUniformNNTime T N (i+1)) ω-B (itoUniformNNTime T N i) ω)

theorem brownianUniformLeftSum_difference_secondMoment {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F t))
    (hFi : ∀ t, MemLp (F t) 2 P) (T : ℝ≥0) (N M : ℕ) (hN : 0 < N) (hM : 0 < M) :
    (∫ ω, (brownianUniformLeftSum (B j) F T N ω-brownianUniformLeftSum (B j) F T M ω)^2 ∂P) =
      (T : ℝ)/(N*M : ℕ)*∑ k : Fin (N*M), ∫ ω,
        (F (itoUniformNNTime T N (k.val/M)) ω-F (itoUniformNNTime T M (k.val/N)) ω)^2 ∂P := by
  have := Fintype.ofFinite ι
  let s := fun k : Fin (N*M) => itoUniformNNTime T (N*M) k
  let d := fun k : Fin (N*M) => itoUniformNNTime T (N*M) (k.val+1)-s k
  let G := fun k : Fin (N*M) => fun ω =>
    F (itoUniformNNTime T N (k.val/M)) ω-F (itoUniformNNTime T M (k.val/N)) ω
  have hend (k : Fin (N*M)) : s k+d k = itoUniformNNTime T (N*M) (k.val+1) :=
    add_tsub_cancel_of_le (itoUniformNNTime_mono T (N*M) (Nat.le_succ k.val))
  have hd (k : Fin (N*M)) : (d k : ℝ) = (T : ℝ)/(N*M : ℕ) :=
    itoUniformNNTime_increment_sub_coe T (N*M) k
  have hG (k : Fin (N*M)) : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB (s k)) _ (G
      k) := by
    have hc1 := itoUniformNNTime_coarse_le_fine T N M k hM
    have hc2 := itoUniformNNTime_coarse_le_fine T M N k hN
    rw [Nat.mul_comm M N] at hc2
    exact ((hF _).mono ((ginibreBrownianAugmentedFiltration B P hB).mono hc1) le_rfl).sub
      ((hF _).mono ((ginibreBrownianAugmentedFiltration B P hB).mono hc2) le_rfl)
  have hchron (i k : Fin (N*M)) (hik : i < k) : s i+d i ≤ s k := by
    rw [hend]
    exact itoUniformNNTime_mono T (N*M) (Nat.succ_le_of_lt hik)
  have hh := ginibreBrownian_augmented_linear_sum_isometry B P hB hind j (N*M) s d hchron G hG
    (fun k => (hFi _).sub (hFi _))
  simp only [hend, hd,← Finset.mul_sum] at hh
  rw [← hh]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro ω
  dsimp only
  congr 1
  simp only [brownianUniformLeftSum]
  rw [
    itoUniformNNWeightedSum_difference_common_grid (fun t => F t ω) (fun t => F t ω) (fun t => B j t
        ω) T N M hN hM]
  simpa only [G, s] using (Fin.sum_univ_eq_sum_range (fun k =>
    (F (itoUniformNNTime T N (k/M)) ω-F (itoUniformNNTime T M (k/N)) ω)*
      (B j (itoUniformNNTime T (N*M) (k+1)) ω-B j (itoUniformNNTime T (N*M) k) ω)) (N*M)).symm

end
end GinibrePoincare
