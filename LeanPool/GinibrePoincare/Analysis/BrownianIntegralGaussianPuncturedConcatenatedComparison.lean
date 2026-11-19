/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralGaussianPuncturedConcatenatedComparison.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGaussianConcatenatedComparison
public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGaussianGridIntegrability
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralApproximationTransfer

/-! Genuine uniform and concatenated grids have the same stochastic limit for
bounded adapted fields continuous at every strictly positive time. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem brownianConcatenated_initial_cutoff_difference {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (F : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0)
    (ε : ℝ) (hε : 0 < ε) (hεs : 2 * ε ≤ (s : ℝ))
    (N : ℕ) (hN : 0 < N) (ω : Ω) :
    brownianActualLeftGridSum B F (itoConcatenatedGrid s t N) (N+N) ω-
      brownianActualLeftGridSum B (brownianInitialTimeCutoff F ε)
        (itoConcatenatedGrid s t N) (N+N) ω =
    brownianUniformLeftSum B F s N ω-
      brownianUniformLeftSum B (brownianInitialTimeCutoff F ε) s N ω := by
  rw [brownianActualLeftGridSum_concatenated B F s t N hN ω,
    brownianActualLeftGridSum_concatenated B (brownianInitialTimeCutoff F ε) s t N hN ω]
  have he : (∑ k ∈ Finset.range N, brownianInitialTimeCutoff F ε (s+itoUniformNNTime t N k) ω*
      (B (s+itoUniformNNTime t N (k+1)) ω-B (s+itoUniformNNTime t N k) ω)) =
      ∑ k ∈ Finset.range N, F (s+itoUniformNNTime t N k) ω*
        (B (s+itoUniformNNTime t N (k+1)) ω-B (s+itoUniformNNTime t N k) ω) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [brownianInitialTimeCutoff_eq F hε _ ω (hεs.trans (by
      change (s : ℝ) ≤ (s : ℝ)+(itoUniformNNTime t N k : ℝ)
      exact le_add_of_nonneg_right (itoUniformNNTime t N k).coe_nonneg))]
  rw [he]
  ring

theorem brownianUniformLeftSum_concatenated_punctured_difference_tendsto_meanSquare
    {Ω ι : Type*} [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ r, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB r) _ (F r))
    (hFi : ∀ r, MemLp (F r) 2 P) (s t : ℝ≥0)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun r => F r ω) (Ioi 0))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ r ω, ‖F r ω‖ ≤ C) :
    Tendsto (fun k => ∫ ω,
      (brownianUniformLeftSum (B j) F (s+t) (k+1) ω-
        brownianActualLeftGridSum (B j) F (itoConcatenatedGrid s t (k+1))
          ((k+1)+(k+1)) ω)^2 ∂P) atTop (𝓝 0) := by
  have := Fintype.ofFinite ι
  by_cases hs : s=0
  · subst s
    have he (k : ℕ) (ω : Ω) : brownianActualLeftGridSum (B j) F
        (itoConcatenatedGrid 0 t (k+1)) ((k+1)+(k+1)) ω =
        brownianUniformLeftSum (B j) F t (k+1) ω := by
      rw [brownianActualLeftGridSum_concatenated _ _ _ _ _ (Nat.succ_pos k)]
      simp [brownianUniformLeftSum, itoUniformNNTime, itoUniformTime]
    simp only [zero_add, he, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), integral_zero]
    exact tendsto_const_nhds
  have hspos : 0 < s := lt_of_le_of_ne bot_le (Ne.symm hs)
  have hstpos : 0 < s+t := add_pos_of_pos_of_nonneg hspos bot_le
  let ε := fun n : ℕ => (s : ℝ)/(4*((n : ℝ)+1))
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεs (n : ℕ) : 2*ε n ≤ (s : ℝ) := by
    dsimp [ε]
    apply (mul_div_assoc 2 (s : ℝ) _ ▸ (div_le_iff₀ (by positivity : 0 < 4*((n : ℝ)+1)))).mpr
    nlinarith [s.coe_nonneg, Nat.cast_nonneg (α := ℝ) n]
  let A := fun k => brownianUniformLeftSum (B j) F (s+t) (k+1)
  let D := fun k => brownianActualLeftGridSum (B j) F (itoConcatenatedGrid s t (k+1)) ((k+1)+(k+1))
  let U := fun n k => brownianUniformLeftSum (B j) (brownianInitialTimeCutoff F (ε n)) (s+t) (k+1)
  let V := fun n k => brownianActualLeftGridSum (B j) (brownianInitialTimeCutoff F (ε n))
    (itoConcatenatedGrid s t (k+1)) ((k+1)+(k+1))
  have hcut (n r) : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB r) _
      (brownianInitialTimeCutoff F (ε n) r) := brownianInitialTimeCutoff_adapted F (ε n) _ hF r
  have hcuti (n r) : MemLp (brownianInitialTimeCutoff F (ε n) r) 2 P := MemLp.of_bound
    ((hcut n r).mono ((ginibreBrownianAugmentedFiltration B P hB).le r) le_rfl).aestronglyMeasurable
        C
    (ae_of_all P (fun ω => brownianInitialTimeCutoff_bound F (ε n) C hbound r ω))
  have hAL (k) : MemLp (A k) 2 P := brownianUniformLeftSum_memLp_two B P hB hind j F hF hFi _ _
  have hDL (k) : MemLp (D k) 2 P := brownianActualLeftGridSum_memLp_two B P hB hind j F hF hFi _
    (itoConcatenatedGrid_monotone s t (k+1) (Nat.succ_pos k)) _
  have hUL (n k) : MemLp (U n k) 2 P := brownianUniformLeftSum_memLp_two B P hB hind j _
    (hcut n) (hcuti n) _ _
  have hVL (n k) : MemLp (V n k) 2 P := brownianActualLeftGridSum_memLp_two B P hB hind j _
    (hcut n) (hcuti n) _ (itoConcatenatedGrid_monotone s t (k+1) (Nat.succ_pos k)) _
  have hAU (n k) : (∫ ω, (A k ω-U n k ω)^2 ∂P) ≤
      C^2*(2*ε n+((s+t : ℝ≥0) : ℝ)/((k : ℝ)+1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using brownianUniformLeftSum_initial_cutoff_error_bound
      B P hB hind j F hF C (ε n) hC (hε n) hbound (s+t) hstpos (k+1) (Nat.succ_pos k)
  have hVD (n k) : (∫ ω, (V n k ω-D k ω)^2 ∂P) ≤
      C^2*(2*ε n+(s : ℝ)/((k : ℝ)+1)) := by
    have he (ω : Ω) : (V n k ω-D k ω)^2 =
        (brownianUniformLeftSum (B j) F s (k+1) ω-
          brownianUniformLeftSum (B j) (brownianInitialTimeCutoff F (ε n)) s (k+1) ω)^2 := by
      have hh := brownianConcatenated_initial_cutoff_difference (B j) F s t (ε n) (hε n) (hεs n)
        (k+1) (Nat.succ_pos k) ω
      dsimp only [V, D]
      calc
        _ = (brownianActualLeftGridSum (B j) F (itoConcatenatedGrid s t (k+1)) ((k+1)+(k+1)) ω-
          brownianActualLeftGridSum (B j) (brownianInitialTimeCutoff F (ε n))
            (itoConcatenatedGrid s t (k+1)) ((k+1)+(k+1)) ω)^2 := by ring
        _ = _ := congrArg (fun x : ℝ => x^2) hh
    simp_rw [he]
    simpa only [Nat.cast_add, Nat.cast_one] using brownianUniformLeftSum_initial_cutoff_error_bound
      B P hB hind j F hF C (ε n) hC (hε n) hbound s hspos (k+1) (Nat.succ_pos k)
  have hUV (n) : Tendsto (fun k => ∫ ω, (U n k ω-V n k ω)^2 ∂P) atTop (𝓝 0) := by
    apply brownianUniformLeftSum_concatenated_difference_tendsto_meanSquare B P hB hind j _
      (hcut n) (hcuti n) s t _ C hC (fun r ω => brownianInitialTimeCutoff_bound F (ε n) C hbound r
          ω)
    filter_upwards [hcont] with ω hc
    exact (brownianInitialTimeCutoff_continuous F (hε n) ω hc).continuousOn
  let v := fun (n k : ℕ) => 4*(C^2*(2*ε n+((s+t : ℝ≥0) : ℝ)/((k : ℝ)+1))+
    (∫ ω, (U n k ω-V n k ω)^2 ∂P)+C^2*(2*ε n+(s : ℝ)/((k : ℝ)+1)))
  apply nonnegative_error_tendsto_of_approximation _ v (fun n => 16*C^2*ε n)
    (fun k => integral_nonneg fun ω => sq_nonneg _)
  · intro n k
    have hh := actualMeanSquare_difference_le_four_errors P (A k) (U n k) (V n k) (D k) (D k)
      (hAL k) (hUL n k) (hVL n k) (hDL k) (hDL k)
    simp only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), integral_zero, add_zero] at hh
    exact hh.trans (by dsimp only [v]; gcongr <;> first | exact hAU n k | exact hVD n k)
  · intro n
    have hm (r : ℝ) : Tendsto (fun k : ℕ => r/((k : ℝ)+1)) atTop (𝓝 0) := by
      simpa only [mul_zero, mul_one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 :=
          ℝ)).const_mul r
    have hh := ((((hm ((s+t : ℝ≥0) : ℝ)).const_add (2*ε n)).const_mul (C^2)).add (hUV n)).add
      (((hm (s : ℝ)).const_add (2*ε n)).const_mul (C^2)) |>.const_mul 4
    convert hh using 1; ring_nf
  · have he : Tendsto ε atTop (𝓝 0) := by
      have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((s : ℝ)/4)
      convert hh using 1 <;> (try funext n) <;> (try dsimp only [ε]) <;> field_simp; ring_nf
    simpa only [mul_zero] using he.const_mul (16*C^2)

end
end GinibrePoincare
