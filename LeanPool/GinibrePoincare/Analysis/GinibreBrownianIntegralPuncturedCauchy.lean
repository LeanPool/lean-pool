/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralPuncturedCauchy.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralFourErrorBound
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralL2Limit

/-! Initial-time-cutoff stochastic integrals are Cauchy in genuine L². -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem brownianInitialCutoff_integral_limits_cauchy {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F t))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t ω, ‖F t ω‖ ≤ C)
    (T : ℝ≥0) (hT : 0 < T) (M : ℕ → Ω → ℝ) (hM : ∀ n, MemLp (M n) 2 P)
    (hlim : ∀ n, Tendsto (fun k => ∫ ω,
      (M n ω - brownianUniformLeftSum (B j) (brownianInitialTimeCutoff F (1 / ((n : ℝ) + 1)))
        T (k + 1) ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun q : ℕ × ℕ => ∫ ω, (M q.1 ω-M q.2 ω)^2 ∂P) atTop (𝓝 0) := by
  have := Fintype.ofFinite ι
  let ε := fun n : ℕ => 1/((n : ℝ)+1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  let S := fun k => brownianUniformLeftSum (B j) F T (k+1)
  let A := fun n k => brownianUniformLeftSum (B j) (brownianInitialTimeCutoff F (ε n)) T (k+1)
  have hFi (t : ℝ≥0) : MemLp (F t) 2 P := MemLp.of_bound
    ((hF t).mono ((ginibreBrownianAugmentedFiltration B P hB).le t) le_rfl).aestronglyMeasurable
    C (ae_of_all P (hb t))
  have hSL (k : ℕ) : MemLp (S k) 2 P :=
    brownianUniformLeftSum_memLp_two B P hB hind j F hF hFi T (k+1)
  have hAL (n k : ℕ) : MemLp (A n k) 2 P := by
    have ha := brownianInitialTimeCutoff_adapted F (ε n) _ hF
    have hi (t : ℝ≥0) : MemLp (brownianInitialTimeCutoff F (ε n) t) 2 P := MemLp.of_bound
      ((ha t).mono ((ginibreBrownianAugmentedFiltration B P hB).le t) le_rfl).aestronglyMeasurable C
      (ae_of_all P (fun ω => brownianInitialTimeCutoff_bound F (ε n) C hb t ω))
    exact brownianUniformLeftSum_memLp_two B P hB hind j _ ha hi T (k+1)
  have herror (n k : ℕ) : (∫ ω, (S k ω-A n k ω)^2 ∂P) ≤
      C^2*(2*ε n+(T : ℝ)/((k : ℝ)+1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      brownianUniformLeftSum_initial_cutoff_error_bound B P hB hind j F hF C (ε n) hC (hε n) hb
        T hT (k+1) (Nat.succ_pos k)
  have hpair (n m : ℕ) : (∫ ω, (M n ω-M m ω)^2 ∂P) ≤ 8*C^2*(ε n+ε m) := by
    have hreverse (k : ℕ) : (∫ ω, (A m k ω-M m ω)^2 ∂P) =
        ∫ ω, (M m ω-A m k ω)^2 ∂P := by
      apply integral_congr_ae
      exact ae_of_all P fun ω => by ring
    let D := fun k => 4*((∫ ω, (M n ω-A n k ω)^2 ∂P)+
      C^2*(2*ε n+(T : ℝ)/((k : ℝ)+1))+
      C^2*(2*ε m+(T : ℝ)/((k : ℝ)+1))+
      (∫ ω, (M m ω-A m k ω)^2 ∂P))
    have hbound (k : ℕ) : (∫ ω, (M n ω-M m ω)^2 ∂P) ≤ D k := by
      have hh := actualMeanSquare_difference_le_four_errors P (M n) (A n k) (S k) (A m k) (M m)
        (hM n) (hAL n k) (hSL k) (hAL m k) (hM m)
      have he (ω : Ω) : (A n k ω-S k ω)^2=(S k ω-A n k ω)^2 := by ring
      simp_rw [he, hreverse] at hh
      exact hh.trans (by dsimp only [D]; gcongr <;> apply herror)
    have hmesh : Tendsto (fun k : ℕ => (T : ℝ)/((k : ℝ)+1)) atTop (𝓝 0) := by
      simpa only [mul_zero, mul_one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (T : ℝ)
    have hDn : Tendsto D atTop (𝓝 (8*C^2*(ε n+ε m))) := by
      have hh := (((hlim n).add ((hmesh.const_add (2*ε n)).const_mul (C^2))).add
        ((hmesh.const_add (2*ε m)).const_mul (C^2))).add (hlim m) |>.const_mul 4
      convert hh using 1; dsimp [D, ε, A]; ring_nf
    exact ge_of_tendsto hDn (Eventually.of_forall hbound)
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hsum : Tendsto (fun q : ℕ × ℕ => ε q.1+ε q.2) atTop (𝓝 0) := by
    simpa only [zero_add, Function.comp_def] using
      (hεlim.comp (show Tendsto Prod.fst (atTop : Filter (ℕ × ℕ)) atTop from by
        simpa only [← prod_atTop_atTop_eq] using tendsto_fst)).add
      (hεlim.comp (show Tendsto Prod.snd (atTop : Filter (ℕ × ℕ)) atTop from by
        simpa only [← prod_atTop_atTop_eq] using tendsto_snd))
  apply squeeze_zero (fun q : ℕ × ℕ => integral_nonneg fun ω => sq_nonneg (M q.1 ω-M q.2 ω)) (fun q
      => hpair q.1 q.2)
  simpa only [mul_zero] using hsum.const_mul (8*C^2)

end
end GinibrePoincare
