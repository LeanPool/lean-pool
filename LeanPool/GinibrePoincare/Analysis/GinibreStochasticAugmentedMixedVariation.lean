/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticAugmentedMixedVariation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticAugmentedMixedSum
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticBrownianQuadraticVariation
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticMeanSquareInProbability

/-! Genuine mean-square and probability convergence of joint-past weighted Brownian quadratic
variation. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

/-- The weighted mixed-increment sum `∑ Fᵢ (B tᵢ₊₁ - B tᵢ) (D tᵢ₊₁ - D tᵢ)` over the uniform
partition of `[0, t]` into `n + 1` steps. -/
def ginibreBrownianAugmentedMixedError {Ω : Type*} (B D : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (n : ℕ) (F : Fin (n + 1) → Ω → ℝ) : Ω → ℝ :=
  fun ω => ∑ i, F i ω*((B (ginibreUniformBrownianTime t n (i.val+1)) ω-
    B (ginibreUniformBrownianTime t n i) ω)*(D (ginibreUniformBrownianTime t n (i.val+1)) ω-
    D (ginibreUniformBrownianTime t n i) ω))

theorem ginibreBrownianAugmentedMixedError_secondMoment_le {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j k : ι) (hjk : j ≠ k) (t : ℝ≥0) (n : ℕ) (F : Fin (n + 1) → Ω → ℝ)
    (hF : ∀ i : Fin (n + 1), @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB
        (ginibreUniformBrownianTime t n i)) _ (F i))
    (C : ℝ) (hbound : ∀ i ω, ‖F i ω‖ ≤ C) :
    (∫ ω, (ginibreBrownianAugmentedMixedError (B j) (B k) t n F ω)^2 ∂P) ≤
      C^2*(t : ℝ)^2/((n : ℝ)+1) := by
  have := Fintype.ofFinite ι
  let s := fun i : Fin (n + 1) => ginibreUniformBrownianTime t n i
  let d := fun i : Fin (n + 1) => ginibreUniformBrownianTime t n (i.val+1)-s i
  have hend (i : Fin (n + 1)) : s i+d i = ginibreUniformBrownianTime t n (i.val+1) :=
    add_tsub_cancel_of_le (ginibreUniformBrownianTime_mono t n (Nat.le_succ i.val))
  have hc (i k : Fin (n + 1)) (hik : i < k) : s i+d i ≤ s k := by
    rw [hend]
    exact ginibreUniformBrownianTime_mono t n (Nat.succ_le_of_lt hik)
  have h := ginibreBrownian_augmented_mixed_sum_secondMoment_le B P hB hind j k hjk (n+1) s d hc F
      hF C hbound
  simp only [hend] at h
  dsimp only [d, s] at h
  simp only [ginibreBrownianUniformTime_increment_coe] at h
  change (∫ ω, (ginibreBrownianAugmentedMixedError (B j) (B k) t n F ω)^2 ∂P) ≤ _ at h
  convert h using 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one]
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp

theorem ginibreBrownianAugmentedMixedError_tendsto_meanSquare {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j k : ι) (hjk : j ≠ k) (t : ℝ≥0) (F : (n : ℕ) → Fin (n + 1) → Ω → ℝ)
    (hF : ∀ (n : ℕ) (i : Fin (n + 1)), @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB
        (ginibreUniformBrownianTime t n i)) _ (F n i))
    (C : ℝ) (hbound : ∀ n i ω, ‖F n i ω‖ ≤ C) :
    Tendsto (fun n => ∫ ω, (ginibreBrownianAugmentedMixedError (B j) (B k) t n (F n) ω)^2 ∂P)
      atTop (nhds 0) := by
  have := Fintype.ofFinite ι
  apply squeeze_zero (fun n => integral_nonneg fun ω => sq_nonneg _)
    (fun n => ginibreBrownianAugmentedMixedError_secondMoment_le B P hB hind j k hjk t n (F n) (hF
        n) C (hbound n))
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (C^2*(t : ℝ)^2)
  simpa only [mul_zero, mul_one_div] using h

theorem ginibreBrownianAugmentedMixedError_memLp_two {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j k : ι) (hjk : j ≠ k) (t : ℝ≥0) (n : ℕ) (F : Fin (n + 1) → Ω → ℝ)
    (hF : ∀ i : Fin (n + 1), @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB
        (ginibreUniformBrownianTime t n i)) _ (F i))
    (C : ℝ) (hbound : ∀ i ω, ‖F i ω‖ ≤ C) :
    MemLp (ginibreBrownianAugmentedMixedError (B j) (B k) t n F) 2 P := by
  have := Fintype.ofFinite ι
  have hX (i : Fin (n + 1)) : MemLp (fun ω => F i ω*((B j (ginibreUniformBrownianTime t n (i.val+1))
      ω-
      B j (ginibreUniformBrownianTime t n i) ω)*(B k (ginibreUniformBrownianTime t n (i.val+1)) ω-
      B k (ginibreUniformBrownianTime t n i) ω))) 2 P := by
    let a := ginibreUniformBrownianTime t n i
    let d := ginibreUniformBrownianTime t n (i.val+1)-a
    have hend : a+d = ginibreUniformBrownianTime t n (i.val+1) :=
      add_tsub_cancel_of_le (ginibreUniformBrownianTime_mono t n (Nat.le_succ i.val))
    have hFM : Measurable (F i) := (hF i).mono ((ginibreBrownianAugmentedFiltration B P hB).le _)
        le_rfl
    have hW : MemLp (F i) 2 P := MemLp.of_bound hFM.aestronglyMeasurable C (Eventually.of_forall
        (hbound i))
    have h := ginibreBrownian_augmented_mixed_memLp_two B P hB hind a d j k hjk (F i) (hF i) hW
    rw [hend] at h
    simpa only [d, a, ginibreBrownianUniformTime_increment_coe] using h
  convert! memLp_finsetSum Finset.univ (fun i _ => hX i) using 1

theorem ginibreBrownianAugmentedMixedError_tendstoInProbability {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j k : ι) (hjk : j ≠ k) (t : ℝ≥0) (F : (n : ℕ) → Fin (n + 1) → Ω → ℝ)
    (hF : ∀ (n : ℕ) (i : Fin (n + 1)), @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB
        (ginibreUniformBrownianTime t n i)) _ (F n i))
    (C : ℝ) (hbound : ∀ n i ω, ‖F n i ω‖ ≤ C) :
    TendstoInMeasure P (fun n => ginibreBrownianAugmentedMixedError (B j) (B k) t n (F n)) atTop
        (fun _ => 0) := by
  have := Fintype.ofFinite ι
  apply ginibre_tendstoInMeasure_of_meanSquare P _ _
  · intro n
    simpa only [sub_zero] using
      (ginibreBrownianAugmentedMixedError_memLp_two B P hB hind j k hjk t n (F n) (hF n) C (hbound
          n)).integrable_sq
  · simpa only [sub_zero] using ginibreBrownianAugmentedMixedError_tendsto_meanSquare B P hB hind j
      k hjk t F hF C hbound

end
end GinibrePoincare
